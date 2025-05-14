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
import minicp.engine.core.Constraint;
import minicp.engine.core.IntVar;
import minicp.util.exception.NotImplementedException;


/**
 *
 * Element Constraint modeling {@code array[y] = z}
 *
 */
public class Element1DDomainConsistent extends AbstractConstraint {

    private final int[] t;
    private final IntVar y;
    private final IntVar z;

    private int[] bufY  = new int[0];
    private int[] bufZ  = new int[0];

    private static int[] ensureCapacity(int[] a, int needed) {
        return (a.length >= needed) ? a : new int[needed];
    }
    /**
     * Creates an element constraint {@code array[y] = z}
     *
     * @param array the array to index
     * @param y the index variable
     * @param z the result variable
     */
    public Element1DDomainConsistent(int[] array, IntVar y, IntVar z) {
        super(y.getSolver());
        this.t = array;
        this.y = y;
        this.z = z;
    }

    @Override
    public void post() {
        propagate();
        y.propagateOnDomainChange(this);
        z.propagateOnDomainChange(this);
    }

    @Override
    public void propagate() {
        bufY = ensureCapacity(bufY, y.size());
        bufZ = ensureCapacity(bufZ, z.size());

        // 1. prune y
        int ySize = y.fillArray(bufY);
        for (int i = 0; i < ySize; i++) {
            int idx = bufY[i];
            if (idx < 0 || idx >= t.length || !z.contains(t[idx])) {
                y.remove(idx);
            }
        }

        // 2. prune z
        int zSize = z.fillArray(bufZ);
        for (int j = 0; j < zSize; j++) {
            int v = bufZ[j];
            boolean supported = false;
            int ySz = y.fillArray(bufY);   // fresh snapshot
            for (int k = 0; k < ySz && !supported; k++)
                supported = (t[bufY[k]] == v);
            if (!supported) z.remove(v);
        }
    }
}
