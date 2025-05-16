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


package minicp.engine.constraints;

import minicp.cp.Factory;
import minicp.engine.core.AbstractConstraint;
import minicp.engine.core.BoolVar;
import minicp.engine.core.IntVar;
import minicp.engine.core.Solver;
import minicp.util.exception.NotImplementedException;

import java.util.Arrays;

import static minicp.cp.Factory.*;

/**
 * Cumulative constraint with sum decomposition (very slow).
 */
public class CumulativeDecomposition extends AbstractConstraint {

    private final IntVar[] start;
    private final int[] duration;
    private final IntVar[] end;
    private final int[] demand;
    private final int capa;

    /**
     * Creates a cumulative constraint with a decomposition into sum constraint.
     * At any time-point t, the sum of the demands
     * of the activities overlapping t do not overlap the capacity.
     *
     * @param start the start time of each activities
     * @param duration the duration of each activities (non negative)
     * @param demand the demand of each activities, non negative
     * @param capa the capacity of the constraint
     */
    public CumulativeDecomposition(IntVar[] start, int[] duration, int[] demand, int capa) {
        super(start[0].getSolver());
        this.start = start;
        this.duration = duration;
        this.end = Factory.makeIntVarArray(start.length, i -> plus(start[i], duration[i]));
        this.demand = demand;
        this.capa = capa;
    }

    @Override
    public void post() {

        int min = Arrays.stream(start).map(s -> s.min()).min(Integer::compare).get();
        int max = Arrays.stream(end).map(e -> e.max()).max(Integer::compare).get();

        for (int t = min; t < max; t++) {

            BoolVar[] overlaps = new BoolVar[start.length];
            for (int i = 0; i < start.length; i++) {
                overlaps[i] = makeBoolVar(getSolver());
                // TODO
                // post the constraints to enforce
                // that overlaps[i] is true iff start[i] <= t && t < start[i] + duration[i]
                // hint: use IsLessOrEqual, introduce BoolVar, use views minus, plus, etc.
                //       logical constraints (such as logical and can be modeled with sum)

                Solver cp = getSolver();

                // b1 (start[i] ≤ t)
                BoolVar b1 = isLessOrEqual(start[i], t);

                // b2 (t < start[i] + duration[i]), t ≤ end[i] − 1
                IntVar  constT     = makeIntVar(cp, t, t);
                IntVar  endMinus1  = minus(end[i], 1);
                BoolVar b2         = makeBoolVar(cp);
                cp.post(new IsLessOrEqualVar(b2, constT, endMinus1));

                // overlaps[i] = b1 ∧ b2
                cp.post(lessOrEqual(overlaps[i], b1));   // overlaps  b1
                cp.post(lessOrEqual(overlaps[i], b2));   // overlaps  b2
                IntVar sum12 = sum(b1, b2);              // b1 + b2
                cp.post(lessOrEqual(sum12, plus(overlaps[i], 1)));  // if b1 & b2 then overlaps = 1
            }

            IntVar[] overlapHeights = Factory.makeIntVarArray(start.length, i -> mul(overlaps[i], demand[i]));
            IntVar cumHeight = sum(overlapHeights);
            cumHeight.removeAbove(capa);

        }

    }
}
