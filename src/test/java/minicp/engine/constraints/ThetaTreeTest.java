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

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ThetaTreeTest {

    @Test
    public void simpleTest0() {
        ThetaTree thetaTree = new ThetaTree(4);
        thetaTree.insert(0, 5, 5);
        assertEquals(5, thetaTree.getECT());
        thetaTree.insert(1, 31, 6);
        assertEquals(31, thetaTree.getECT());
        thetaTree.insert(2, 30, 4);
        assertEquals(35, thetaTree.getECT());
        thetaTree.insert(3, 42, 10);
        assertEquals(45, thetaTree.getECT());
        thetaTree.remove(3);
        assertEquals(35, thetaTree.getECT());
        thetaTree.reset();
        assertEquals(Integer.MIN_VALUE, thetaTree.getECT());
    }

    @Test
    public void simpleTest1() {
        ThetaTree thetaTree = new ThetaTree(4);

        // manually computed ECT progression
        thetaTree.insert(0, 10, 5);
        assertEquals(10, thetaTree.getECT());

        thetaTree.insert(1, 15, 3);
        assertEquals(15, thetaTree.getECT());

        thetaTree.insert(2, 12, 4);
        assertEquals(19, thetaTree.getECT());

        thetaTree.insert(3, 18, 2);
        assertEquals(21, thetaTree.getECT());

        thetaTree.remove(1);
        assertEquals(18, thetaTree.getECT());

        thetaTree.reset();
        assertEquals(Integer.MIN_VALUE, thetaTree.getECT());
    }
}
