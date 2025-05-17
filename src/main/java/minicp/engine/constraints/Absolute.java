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
        propagate();
        x.whenDomainChange(this::propagate);
        y.whenDomainChange(this::propagate);
    }

    @Override
    public void propagate() {
        // y = |x|
        // TODO
        int minAbs = Math.min(Math.abs(x.min()), Math.abs(x.max()));
        int maxAbs = Math.max(Math.abs(x.min()), Math.abs(x.max()));
        y.removeBelow(minAbs);
        y.removeAbove(maxAbs);

        // 2. bound x with respect to current
        int yMin = y.min();
        int yMax = y.max();
        x.removeBelow(-yMax);
        x.removeAbove(yMax);
        while (x.min() < -yMax || (x.min() > -yMin && x.min() < yMin)) {
            x.remove(x.min());
        }
        while (x.max() > yMax || (x.max() < yMin && x.max() > -yMin)) {
            x.remove(x.max());
        }
        setActive(!x.isFixed() || !y.isFixed());
    }
}


