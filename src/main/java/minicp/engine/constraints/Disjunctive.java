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
import minicp.util.exception.InconsistencyException;
import minicp.util.exception.NotImplementedException;

import java.util.Arrays;
import java.util.Comparator;

import static minicp.cp.Factory.*;

/**
 * Disjunctive Scheduling Constraint:
 * Any two pairs of activities cannot overlap in time.
 */
public class Disjunctive extends AbstractConstraint {

    private final IntVar[] start;
    private final int[] duration;
    private final IntVar[] end;


    private final Integer[] permLct;
    private final Integer[] permEst;
    private final int[] rankEst;
    private final int[] startMin;
    private final int[] endMax;

    private final ThetaTree thetaTree;
    private final boolean postMirror;


    /**
     * Creates a disjunctive constraint that enforces
     * that for any two pair i,j of activities we have
     * {@code start[i]+duration[i] <= start[j] or start[j]+duration[j] <= start[i]}.
     *
     * @param start the start times of the activities
     * @param duration the durations of the activities
     */
    public Disjunctive(IntVar[] start, int[] duration) {
        this(start, duration, true);
    }


    private Disjunctive(IntVar[] start, int[] duration, boolean postMirror) {
        super(start[0].getSolver());
        this.postMirror = postMirror;
        this.start = start;
        this.duration = duration;
        this.end = Factory.makeIntVarArray(start.length, i -> plus(start[i], duration[i]));

        startMin = new int[start.length];
        endMax = new int[start.length];
        permEst = new Integer[start.length];
        permLct = new Integer[start.length];
        rankEst = new int[start.length];
        for (int i = 0; i < start.length; i++) {
            permEst[i] = i;
            permLct[i] = i;
        }
        thetaTree = new ThetaTree(start.length);

    }


    @Override
    public void post() {

        for (int i = 0; i < start.length; i++) {
            start[i].propagateOnBoundChange(this);
        }

        int[] demands = new int[start.length];
        for (int i = 0; i < start.length; i++) {
            demands[i] = 1;
        }
        getSolver().post(new Cumulative(start, duration, demands, 1), false);


        // TODO 1: replace by posting binary decomposition (DisjunctiveBinary) using IsLessOrEqualVar
        for (int i = 0; i < start.length; i++) {
            for (int j = i + 1; j < start.length; j++) {
                getSolver().post(new DisjunctiveBinary(start[i], duration[i], start[j], duration[j]), false);
            }
        }

        // TODO 2: add the mirror filtering as done in the Cumulative Constraint
        if (postMirror) {
            IntVar[] startMirror = Factory.makeIntVarArray(start.length, k -> minus(end[k]));
            getSolver().post(new Disjunctive(startMirror, duration, false), false);
        }

        propagate();
    }

    @Override
    public void propagate() {
        // HINT: for the TODO 3-6 you'll need the ThetaTree data-structure

        // TODO 3: read and understand the OverLoadCheck algorithm implementation

        // TODO 4: add the Detectable Precedences algorithm

        // TODO 5: add the Not-Last algorithm

        // TODO 6 (optional): implement the Lambda-Theta tree and implement the Edge-Finding

        boolean changed = true;
        while (changed) {
            overLoadChecker();
            changed = detectablePrecedence();
            // Java has short-circuit evaluation: notLast will only be called if changed is false.
            changed = changed || notLast();
        }

    }

    private void update() {
        Arrays.sort(permEst, Comparator.comparingInt(i -> start[i].min()));
        for (int i = 0; i < start.length; i++) {
            rankEst[permEst[i]] = i;
            startMin[i] = start[i].min();
            endMax[i] = end[i].max();
        }
    }

    public void overLoadChecker() {
        update();
        Arrays.sort(permLct, Comparator.comparingInt(i -> end[i].max()));
        thetaTree.reset();
        for (int i = 0; i < start.length; i++) {
            int activity = permLct[i];
            thetaTree.insert(rankEst[activity], end[activity].min(), duration[activity]);
            if (thetaTree.getECT() > end[activity].max()) {
                throw new InconsistencyException();
            }
        }
    }

    /**
     * @return true if one domain was changed by the detectable precedence algo
     */
    public boolean detectablePrecedence() {
        update();
        Arrays.sort(permLct, Comparator.comparingInt(i -> end[i].max()));
        thetaTree.reset();
        int k = 0;
        boolean changed = false;

        for (int idx = 0; idx < start.length; idx++) {
            int j = permLct[idx];

            while (k < start.length && startMin[permEst[k]] + duration[permEst[k]] <= end[j].max()) {
                int a = permEst[k];
                if (a != j) {
                    thetaTree.insert(rankEst[a], startMin[a] + duration[a], duration[a]);
                }
                k++;
            }

            thetaTree.remove(rankEst[j]);
            int ect = thetaTree.getECT();
            if (ect > start[j].min()) {
                start[j].removeBelow(ect);
                startMin[j] = start[j].min();
                changed = true;
            }
            thetaTree.insert(rankEst[j], startMin[j] + duration[j], duration[j]);
        }

        return changed;
    }

    /**
     * @return true if one domain was changed by the not-last algo
     */
    public boolean notLast() {
        update();
        Arrays.sort(permEst, Comparator.comparingInt(i -> start[i].min()));
        Arrays.sort(permLct, Comparator.comparingInt(i -> end[i].max()));

        thetaTree.reset();
        int k = start.length - 1;
        boolean changed = false;

        for (int idx = start.length - 1; idx >= 0; idx--) {
            int j = permEst[idx];

            while (k >= 0 && end[permLct[k]].max() > startMin[j]) {
                int a = permLct[k];
                if (a != j) {
                    thetaTree.insert(rankEst[a], endMax[a] - duration[a], duration[a]);
                }
                k--;
            }

            thetaTree.remove(rankEst[j]);
            int ect = thetaTree.getECT();
            if (ect > endMax[j] - duration[j]) {
                end[j].removeAbove(ect);
                endMax[j] = end[j].max();
                changed = true;
            }
            thetaTree.insert(rankEst[j], endMax[j] - duration[j], duration[j]);
        }

        return changed;
    }
}
