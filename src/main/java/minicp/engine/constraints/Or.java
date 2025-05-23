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

import static minicp.util.exception.InconsistencyException.INCONSISTENCY;
import minicp.util.exception.NotImplementedException;

/**
 * Logical or constraint {@code  x1 or x2 or ... xn}
 */
public class Or extends AbstractConstraint { // x1 or x2 or ... xn

    private final BoolVar[] x;
    private final int n;
    private StateInt wL; // watched literal left
    private StateInt wR; // watched literal right


    /**
     * Creates a logical or constraint: at least one variable is true:
     * {@code  x1 or x2 or ... xn}
     *
     * @param x the variables in the scope of the constraint
     */
    public Or(BoolVar[] x) {
        super(x[0].getSolver());
        this.x = x;
        this.n = x.length;
        wL = getSolver().getStateManager().makeStateInt(0);
        wR = getSolver().getStateManager().makeStateInt(n - 1);
    }

    @Override
    public void post() {
        propagate();
    }


    @Override
    public void propagate() {
        // update watched literals
        // TODO: implement the filtering using watched literal technique and make sure you pass all the tests
        int left  = wL.value();
        int right = wR.value();

        // shift wl to the first literal that is not fixed-to-false
        while (left < n && x[left].isFixed() && x[left].isFalse()) {
            left++;
        }
        wL.setValue(left);

        // shift wr to the last literal that is not fixed-to-false
        while (right >= left && x[right].isFixed() && x[right].isFalse()) {
            right--;
        }
        wR.setValue(right);

        // true as soon as literal is true
        if (left <= right && (x[left].isTrue() || x[right].isTrue())) {
            setActive(false);
            return;
        }

        // all literals fixed to 0 -> contradiction
        if (left > right) {
            throw INCONSISTENCY;
        }

        // unit clause, only one literal left
        if (left == right) {
            x[left].fix(true);
            setActive(false);
            return;
        }

        x[left].propagateOnFix(this);
        x[right].propagateOnFix(this);
    }
}
