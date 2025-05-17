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
import minicp.engine.core.Solver;
import minicp.engine.core.Constraint;

/**
 * Absolute value constraint
 */
public class Absolute extends AbstractConstraint {

    private final IntVar x;
    private final IntVar y;

    private int[] bufX = new int[0];
    private int[] bufY = new int[0];

    private static int[] ensureCapacity(int[] a, int needed) {
        return (a.length >= needed) ? a : new int[needed];
    }

    /**
     * Creates the absolute value constraint {@code y = |x|}.
     *
     * @param x the input variable such that its absolut value is equal to y
     * @param y the variable that represents the absolute value of x
     */
    public Absolute(IntVar x, IntVar y) {
        super(x.getSolver());
        this.x = x;
        this.y = y;
    }

    public void post() {
        // TODO
        x.propagateOnDomainChange(this);
        y.propagateOnDomainChange(this);
        propagate();
    }

    @Override
    public void propagate() {
        // y = |x|
        // TODO
        bufX = ensureCapacity(bufX, x.size());
        bufY = ensureCapacity(bufY, y.size());

        int xSize = x.fillArray(bufX);
        int ySize = y.fillArray(bufY);

        // 1. prune values of y that have no support in x or are negative
        for (int i = 0; i < ySize; i++) {
            int v = bufY[i];
            if (v < 0) {
                y.remove(v);
            } else {
                boolean supported = false;
                for (int j = 0; j < xSize && !supported; j++)
                    supported = Math.abs(bufX[j]) == v;
                if (!supported) y.remove(v);
            }
        }


        y.fillArray(bufY); // refresh y domain

        // 2. prune values of x that have no support in y
        for (int j = 0; j < xSize; j++) {
            int xv = bufX[j];
            if (!y.contains(Math.abs(xv))) x.remove(xv);
        }
        setActive(!x.isFixed() || !y.isFixed());

        if (x.isFixed() && y.isFixed())
            setActive(false);
    }
}



