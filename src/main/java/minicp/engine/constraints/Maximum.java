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
import minicp.engine.core.*;
import java.util.Arrays;

/**
 * Maximum Constraint
 */
public class Maximum extends AbstractConstraint {

    private final IntVar[] x;
    private final IntVar y;

    /**
     * Creates the maximum constraint y = maximum(x[0],x[1],...,x[n])?
     *
     * @param x the variable on which the maximum is to be found
     * @param y the variable that is equal to the maximum on x
     */
    public Maximum(IntVar[] x, IntVar y) {
        super(x[0].getSolver());
        assert (x.length > 0);
        this.x = x;
        this.y = y;
    }


    @Override
    public void post() {
        // TODO
        //  - call the constraint on all bound changes for the variables (x.propagateOnBoundChange(this))
        //  - call a first time the propagate() method to trigger the propagation

        for (IntVar xi : x) xi.propagateOnBoundChange(this);
        y.propagateOnBoundChange(this);
        propagate();                        // first round
    }


    @Override
    public void propagate() {
        // TODO
        //  - update the min and max values of each x[i] based on the bounds of y
        //  - update the min and max values of each y based on the bounds of all x[i]

        // 1. tighten the bounds of y from the x
        int maxOfMins = x[0].min();
        int maxOfMaxs = x[0].max();
        for (int i = 1; i < x.length; i++) {
            maxOfMins = Math.max(maxOfMins, x[i].min());
            maxOfMaxs = Math.max(maxOfMaxs, x[i].max());
        }
        y.removeBelow(maxOfMins);
        y.removeAbove(maxOfMaxs);

        // 2. tighten the upper bound of every x[i] from y
        int yMax = y.max();
        for (IntVar xi : x)
            xi.removeAbove(yMax);

        // 3. if y.min() cannot be reached by the *other* variables,
        // the current x[i] must take it (lower‑bound pruning)
        int yMin = y.min();

        // find highest and second‑highest
        int max1 = -Integer.MAX_VALUE;
        int max2 = -Integer.MAX_VALUE;
        int cnt1 = 0;
        for (IntVar xi : x) {
            int m = xi.max();
            if (m > max1) { max2 = max1; max1 = m; cnt1 = 1; }
            else if (m == max1) cnt1++;
            else if (m > max2)  max2 = m;
        }

        for (IntVar xi : x) {
            int othersMax = (xi.max() == max1 && cnt1 == 1) ? max2 : max1;
            if (yMin > othersMax)   // only xi can reach yMin
                xi.removeBelow(yMin);
        }

        // 4. deactivate when everything is fixed
//        if (y.isFixed()) {
//            boolean allOk = Arrays.stream(x).allMatch(IntVar::isFixed);
//            if (allOk) setActive(false);
//        }
    }
}
