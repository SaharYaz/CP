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

import minicp.engine.core.AbstractConstraint;
import minicp.engine.core.BoolVar;
import minicp.state.StateInt;
import minicp.util.exception.NotImplementedException;
import static minicp.util.exception.InconsistencyException.INCONSISTENCY;

/**
 * Reified logical or constraint
 */
public class IsOr extends AbstractConstraint { // b <=> x1 or x2 or ... xn

    private final BoolVar b;
    private final BoolVar[] x;
    private final int n;

    private int[] freeVarIndex;
    private StateInt nFreeVars;

    private final Or or;
    private boolean orPosted = false;

    /**
     * Creates a constraint such that
     * the boolean b is true if and only if
     * at least variable in x is true.
     *
     * @param b the boolean that is true if at least one variable in x is true
     * @param x an non empty array of variables
     */
    public IsOr(BoolVar b, BoolVar[] x) {
        super(b.getSolver());
        this.b = b;
        this.x = x;
        this.n = x.length;
        or = new Or(x);

        nFreeVars = getSolver().getStateManager().makeStateInt(n);
        freeVarIndex = new int[n];
        for (int i = 0; i < n; i++) {
            freeVarIndex[i] = i;
        }
    }

    @Override
    public void post() {
        b.propagateOnFix(this);
        for (BoolVar xi : x) {
            xi.propagateOnFix(this);
        }
        propagate();
    }

    private void postOrIfNeeded() {
        if (!orPosted) {
            getSolver().post(or);
            orPosted = true;
        }
    }

    @Override
    public void propagate() {
        // TODO Implement the constraint as efficiently as possible and make sure you pass all the tests

        if (b.isTrue()) {           // b = 1
            postOrIfNeeded();
            return;
        }

        if (b.isFalse()) {          // b = 0
            for (BoolVar xi : x) {
                if (xi.isTrue())            // contradiction
                    throw INCONSISTENCY;
                if (!xi.isFixed())
                    xi.fix(false);
            }
            nFreeVars.setValue(0);
            return;
        }

        // update the set of free variables and detect if one is true
        boolean someTrue = false;
        int nFree = nFreeVars.value();
        for (int i = 0; i < nFree; ) {
            int idx = freeVarIndex[i];
            if (x[idx].isTrue()) {
                someTrue = true;
                break;
            }
            if (x[idx].isFixed()) { // fixed to false
                freeVarIndex[i] = freeVarIndex[nFree - 1];
                freeVarIndex[nFree - 1] = idx;
                nFreeVars.decrement();
                nFree--; // do not increment i to reprocess swapped element
            } else {
                i++; // still free
            }
        }

        if (someTrue) {              // clause satisfied
            b.fix(true);
            postOrIfNeeded();
            return;
        }

        if (nFreeVars.value() == 0) { // all xi are 0
            b.fix(false);
        }

    }
}
