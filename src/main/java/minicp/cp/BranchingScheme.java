/*
 * mini-cp is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License  v3
 * as published by the Free Software Foundation.
 *
 * mini-cp is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY.
 * See the GNU Lesser General Public License  for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with mini-cp. If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
 *
 * Copyright (c)  2018. by Laurent Michel, Pierre Schaus, Pascal Van Hentenryck
 */

package minicp.cp;

import minicp.engine.core.IntVar;
import minicp.engine.core.Solver;
import minicp.search.LimitedDiscrepancyBranching;
import minicp.search.Sequencer;
import minicp.util.Procedure;
import minicp.util.exception.InconsistencyException;
import minicp.util.exception.NotImplementedException;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;

import static minicp.cp.Factory.equal;
import static minicp.cp.Factory.notEqual;
import minicp.state.State;
import minicp.state.StateManager;

/**
 * Factory for search procedures.
 *
 * <p>A typical custom search on an array of variable {@code q} is illustrated next</p>
 *  <pre>
 * {@code
 * DFSearch search = Factory.makeDfs(cp, () -> {
 *   int idx = -1; // index of the first variable that is not fixed
 *   for (int k = 0; k < q.length; k++)
 *      if(q[k].size() > 1) {
 *        idx=k;
 *        break;
 *      }
 *   if(idx == -1)
 *      return new Procedure[0];
 *   else {
 *      IntVar qi = q[idx];
 *      int v = qi.min();
 *      Procedure left = () -> Factory.equal(qi, v);
 *      Procedure right = () -> Factory.notEqual(qi, v);
 *      return branch(left,right);
 *   }
 * });
 * }
 * </pre>
 * @see Factory#makeDfs(Solver, Supplier)
 */
public final class BranchingScheme {

    private BranchingScheme() {
        throw new UnsupportedOperationException();
    }

    /**
     * Constant that should be returned
     * to notify the solver that there are no branches
     * to create any more and that the current state should
     * be considered as a solution.
     * @see Factory#makeDfs(Solver, Supplier)
     */
    public static final Procedure[] EMPTY = new Procedure[0];

    /**
     *
     * @param branches the ordered closures for the child branches
     *                 ordered from left to right in the depth first search.
     *
     * @return an array with those branches
     * @see minicp.search.DFSearch
     */
    public static Procedure[] branch(Procedure... branches) {
        return branches;
    }

    /**
     * Minimum selector.
     * <p>Example of usage.
     * <pre>
     * {@code
     * IntVar xs = selectMin(x,xi -> xi.size() > 1,xi -> xi.size());
     * }
     * </pre>
     *
     * @param x the array on which the minimum value is searched
     * @param p the predicate that filters the element eligible for selection
     * @param f the evaluation function that returns a comparable when applied on an element of x
     * @param <T> the type of the elements in x, for instance {@link IntVar}
     * @param <N> the type on which the minimum is computed, for instance {@link Integer}
     * @return the minimum element in x that satisfies the predicate p
     *         or null if no element satisfies the predicate.
     */
    public static <T, N extends Comparable<N>> T selectMin(T[] x, Predicate<T> p, Function<T, N> f) {
        T sel = null;
        for (T xi : x) {
            if (p.test(xi)) {
                sel = sel == null || f.apply(xi).compareTo(f.apply(sel)) < 0 ? xi : sel;
            }
        }
        return sel;
    }

    /**
     * First-Fail strategy.
     * It selects the first variable with a domain larger than one.
     * Then it creates two branches. The left branch
     * assigning the variable to its minimum value.
     * The right branch removing this minimum value from the domain.
     * @param x the variable on which the first fail strategy is applied.
     * @return a first-fail branching strategy
     * @see Factory#makeDfs(Solver, Supplier)
     */
    public static Supplier<Procedure[]> firstFail(IntVar... x) {
        return () -> {
            IntVar xs = selectMin(x,
                    xi -> xi.size() > 1,
                    xi -> xi.size());
            if (xs == null)
                return EMPTY;
            else {
                int v = xs.min();
                return branch(() -> xs.getSolver().post(equal(xs, v)),
                        () -> xs.getSolver().post(notEqual(xs, v)));
            }
        };
    }

    /**
     * Sequential Search combinator that linearly
     * considers a list of branching generator.
     * One branching of this list is executed
     * when all the previous ones are exhausted (they return an empty array).
     * @param choices the branching schemes considered sequentially in the sequential by
     *                path in the search tree
     * @return a branching scheme implementing the sequential search
     * @see Sequencer
     */
    public static Supplier<Procedure[]> and(Supplier<Procedure[]>... choices) {
        return new Sequencer(choices);
    }

    /**
     * Limited Discrepancy Search combinator
     * that limits the number of right decisions
     * @param branching a branching scheme
     * @param maxDiscrepancy a discrepancy limit (non negative number)
     * @return a branching scheme that cuts off any path accumulating
     *         a discrepancy beyond the limit maxDiscrepancy
     * @see LimitedDiscrepancyBranching
     */
    public static Supplier<Procedure[]> limitedDiscrepancy(Supplier<Procedure[]> branching, int maxDiscrepancy) {
        return new LimitedDiscrepancyBranching(branching, maxDiscrepancy);
    }

    /**
     * Last conflict heuristic
     * Attempts to branch first on the last variable that caused an Inconsistency
     *
     * Lecoutre, C., Saïs, L., Tabary, S.,  Vidal, V. (2009).
     * Reasoning from last conflict (s) in constraint programming.
     * Artificial Intelligence, 173(18), 1592-1614.
     *
     * @param variableSelector returns the next variable to fix
     * @param valueSelector given a variable, returns the value to which
     *                      it must be assigned on the left branch (and excluded on the right)
     */
    public static Supplier<Procedure[]> lastConflict(Supplier<IntVar> variableSelector, Function<IntVar, Integer> valueSelector) {
        final java.util.concurrent.atomic.AtomicReference<IntVar> last = new java.util.concurrent.atomic.AtomicReference<>(null);


        return new Supplier<Procedure[]>() {

            @Override
            public Procedure[] get() {
                IntVar x = last.get();
                if (x == null || x.isFixed()) {
                    x = variableSelector.get();
                    if (x == null)
                        return EMPTY; // no variable left -> solution reached
                }

                final IntVar var = x;               // variable to branch on
                final int val = valueSelector.apply(var);
                final Solver cp = var.getSolver();

                // create the two decision alternatives with LC bookkeeping
                Procedure left = () -> doDecision(cp, var, () -> cp.post(equal(var, val)));
                Procedure right = () -> doDecision(cp, var, () -> cp.post(notEqual(var, val)));

                return branch(left, right);
            }

            // Posts the decision and updates the last conflict variable
            private void doDecision(Solver cp, IntVar var, Procedure post) throws InconsistencyException {
                try {
                    post.call();           // the decision succeeds
                    if (last.get() == var && var.isFixed()) {
                        last.set(null);
                    }
                    // else: keep the last-conflict variable
                } catch (InconsistencyException f) {
                    last.set(var);         // remember the culprit
                    throw f;               // propagate the failure
                }
            }
        };
    }

    /**
     * Conflict Ordering Search
     *
     * Gay, S., Hartert, R., Lecoutre, C.,  Schaus, P. (2015).
     * Conflict ordering search for scheduling problems.
     * In International conference on principles and practice of constraint programming (pp. 140-148).
     * Springer.
     *
     * @param variableSelector returns the next variable to fix
     * @param valueSelector given a variable, returns the value to which
     *                      it must be assigned on the left branch (and excluded on the right)
     */
    public static Supplier<Procedure[]> conflictOrderingSearch(Supplier<IntVar> variableSelector, Function<IntVar, Integer> valueSelector) {

        return new Supplier<Procedure[]>() {

            // Global list of variables ordered by most-recent conflict
            private final java.util.LinkedList<IntVar> order = new java.util.LinkedList<>();

            @Override
            public Procedure[] get() {

                IntVar x = null;
                for (IntVar v : order) {       // first unfixed in list
                    if (!v.isFixed()) { x = v; break; }
                }

                if (x == null) {         // fallback heuristic
                    x = variableSelector.get();
                    if (x == null)       // all vars fixed
                        return EMPTY;
                    if (!order.contains(x))      // add once, at the end
                        order.addLast(x);
                }

                final IntVar var = x;        // captured for lambdas
                final int    v   = valueSelector.apply(var);

                Procedure left  = () -> postDecision(var,
                        () -> var.getSolver().post(equal   (var, v)));
                Procedure right = () -> postDecision(var,
                        () -> var.getSolver().post(notEqual(var, v)));

                return branch(left, right);
            }

            // Posts the decision; on failure moves <var> to the front of the list
            private void postDecision(IntVar var, Procedure post) throws InconsistencyException {
                try {
                    post.call();
                } catch (InconsistencyException f) {
                    order.remove(var);
                    order.addFirst(var);
                    throw f;
                }
            }
        };
    }

}
