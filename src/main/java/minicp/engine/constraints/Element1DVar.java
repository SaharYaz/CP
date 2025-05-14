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
import minicp.util.exception.NotImplementedException;

public class Element1DVar extends AbstractConstraint {

    private final IntVar[] array;
    private final IntVar y;
    private final IntVar z;

    private int[] bufY = new int[0];

    public Element1DVar(IntVar[] array, IntVar y, IntVar z) {
        super(y.getSolver());
        this.array = array;
        this.y = y;
        this.z = z;

    }

    private static int[] ensure(int[] a, int need) {
        return (a.length >= need) ? a : new int[need];
    }

    @Override
    public void post() {
        y.propagateOnDomainChange(this);
        z.propagateOnDomainChange(this);
        for (IntVar v : array)
            v.propagateOnDomainChange(this);

        propagate();
    }

    @Override
    public void propagate() {
        // 1) Gather all current indices of y
        bufY = ensure(bufY, y.size());
        int ny = y.fillArray(bufY);

        // We'll track the overall min/max of array[idx] among surviving idx
        int newMin = Integer.MAX_VALUE;
        int newMax = Integer.MIN_VALUE;

        for (int k = 0; k < ny; k++) {
            int idx = bufY[k];
            // out-of-range
            if (idx < 0 || idx >= array.length) {
                y.remove(idx);
                continue;
            }
            IntVar xi = array[idx];
            // no interval overlap ⇒ no support
            if (xi.max() < z.min() || xi.min() > z.max()) {
                y.remove(idx);
                continue;
            }
            // record for tightening z
            newMin = Math.min(newMin, xi.min());
            newMax = Math.max(newMax, xi.max());
        }


        // 2) Tighten z to the gathered [newMin..newMax]
        z.removeBelow(newMin);
        z.removeAbove(newMax);

        // 3) Bound-consistency on each array[idx] still reachable
        int zmin = z.min();
        int zmax = z.max();
        int ny2  = y.fillArray(bufY);
        for (int k = 0; k < ny2; k++) {
            IntVar xi = array[bufY[k]];
            xi.removeBelow(zmin);
            xi.removeAbove(zmax);
        }

        // 4) If everything is fixed, we can sleep
        if (y.isFixed() && z.isFixed() && array[y.min()].isFixed())
            setActive(false);
    }

}
