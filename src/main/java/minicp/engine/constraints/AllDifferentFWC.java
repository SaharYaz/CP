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
import minicp.engine.core.IntVar;
import minicp.state.StateInt;
import minicp.state.StateManager;

import minicp.util.exception.NotImplementedException;

import java.util.stream.IntStream;

/**
 * Forward Checking filtering AllDifferent Constraint
 *
 * Whenever one variable is fixed, this value
 * is removed from the domain of other variables.
 * This filtering is weaker than the {@link AllDifferentDC}
 * but executes faster.
 */
public class AllDifferentFWC extends AbstractConstraint {

    private IntVar[] x;

    private final int[] dense;
    private final int[] sparse;

    private final StateInt nActive;

    public AllDifferentFWC(IntVar... x) {
        super(x[0].getSolver());
        this.x = x;
        int n = x.length;
        dense  = new int[n];
        sparse = new int[n];
        for (int i = 0; i < n; i++) {
            dense[i]  = i;
            sparse[i] = i;
        }
        StateManager sm = x[0].getSolver().getStateManager();
        nActive = sm.makeStateInt(n);  // initially every variable is active
    }

    @Override
    public void post() {
        for (IntVar xi : x) xi.propagateOnFix(this);
        propagate();
    }

    @Override
    public void propagate() {
        // TODO use the sparse-set trick as seen in Sum.java
        int n = nActive.value();
        int i = 0;
        while (i < n) {
            int varIdx = dense[i];
            IntVar xi  = x[varIdx];

            if (xi.isFixed()) {
                int v = xi.min();

                // delete v from the domain
                for (int j = 0; j < n; j++) {
                    int otherIdx = dense[j];
                    if (otherIdx != varIdx) {
                        x[otherIdx].remove(v);
                    }
                }

                // remove this variable from the active set
                int lastIdx = dense[n - 1];
                dense[i]    = lastIdx;
                sparse[lastIdx] = i;
                dense[n - 1] = varIdx;
                sparse[varIdx] = n - 1;
                n--;
                nActive.setValue(n);
                // we swapped in a new element at position i
            } else {
                i++;
            }
        }
    }
}
