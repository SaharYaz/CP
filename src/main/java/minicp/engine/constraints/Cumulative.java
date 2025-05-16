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
import minicp.engine.constraints.Profile.Rectangle;
import minicp.engine.core.AbstractConstraint;
import minicp.engine.core.IntVar;
import minicp.util.exception.InconsistencyException;

import java.util.ArrayList;

import static minicp.cp.Factory.minus;
import static minicp.cp.Factory.plus;
import minicp.util.exception.NotImplementedException;

/**
 * Cumulative constraint with time-table filtering
 */
public class Cumulative extends AbstractConstraint {

    private final IntVar[] start;
    private final int[] duration;
    private final IntVar[] end;
    private final int[] demand;
    private final int capa;
    private final boolean postMirror;


    /**
     * Creates a cumulative constraint with a time-table filtering.
     * At any time-point t, the sum of the demands
     * of the activities overlapping t do not overlap the capacity.
     *
     * @param start the start time of each activity
     * @param duration the duration of each activity (non negative)
     * @param requirement the requirement of each activity, non negative
     * @param capa the capacity of the constraint
     */
    public Cumulative(IntVar[] start, int[] duration, int[] requirement, int capa) {
        this(start, duration, requirement, capa, true);
    }

    private Cumulative(IntVar[] start, int[] duration, int[] requirement, int capa, boolean postMirror) {
        super(start[0].getSolver());
        this.start = start;
        this.duration = duration;
        this.end = Factory.makeIntVarArray(start.length, i -> plus(start[i], duration[i]));
        this.demand = requirement;
        this.capa = capa;
        this.postMirror = postMirror;
    }


    @Override
    public void post() {
        for (int i = 0; i < start.length; i++) {
            start[i].propagateOnBoundChange(this);
        }

        if (postMirror) {
            IntVar[] startMirror = Factory.makeIntVarArray(start.length, i -> minus(end[i]));
            getSolver().post(new Cumulative(startMirror, duration, demand, capa, false), false);
        }

        propagate();
    }

    @Override
    public void propagate() {
        Profile profile = buildProfile();
        // TODO 2: check that the profile is not exceeding the capa otherwise throw an INCONSISTENCY
        for (int i = 0; i < profile.size(); i++) {
            if (profile.get(i).height() > capa) {
                throw InconsistencyException.INCONSISTENCY;
            }
        }

        for (int i = 0; i < start.length; i++) {
            if (!start[i].isFixed()) {
                // j is the index of the profile rectangle overlapping t
                // int j = profile.rectangleIndex(start[i].min());
                // TODO 3: postpone i to a later point in time
                // hint:
                // Check that at every point in the interval
                // [start[i].getMin() ... start[i].getMin()+duration[i]-1]
                // there is enough remaining capacity.
                // You may also have to check the following profile rectangle(s).
                // Note that the activity you are currently postponing
                // may have contributed to the profile.

                int mandStart = start[i].max();
                int mandEnd   = start[i].min() + duration[i];
                int t         = start[i].min();

                while (true) {
                    boolean fits = true;
                    int tEnd = t + duration[i];

                    // index of the rectangle that overlaps t
                    int j = profile.rectangleIndex(t);

                    // scan successive rectangles until we cover
                    while (j < profile.size() && profile.get(j).start() < tEnd) {
                        Profile.Rectangle rect = profile.get(j);
                        int rectHeight = rect.height();

                        // subtract i's demand if its mandatory part is already counted in this rectangle
                        if (mandStart < rect.end() && mandEnd > rect.start()) {
                            rectHeight -= demand[i];
                        }
                        // not enough remaining capacity
                        if (rectHeight + demand[i] > capa) {
                            t = rect.end();
                            fits = false;
                            break;
                        }
                        j++;
                    }
                    if (fits) break;   // the whole interval fits
                }
                // tighten the lower bound
                if (t > start[i].min()) {
                    start[i].removeBelow(t);
                }

            }
        }
    }

    public Profile buildProfile() {
        ArrayList<Rectangle> mandatoryParts = new ArrayList<Rectangle>();
        for (int i = 0; i < start.length; i++) {
            // TODO 1: add mandatory part of activity i if any
            int mandStart = start[i].max();                 // latest start in current domain
            int mandEnd   = start[i].min() + duration[i];   // earliest end  (exclusive)
            if (mandStart < mandEnd) {                      // activity really has a mandatory part
                mandatoryParts.add(new Rectangle(mandStart, mandEnd, demand[i]));
            }        }
        return new Profile(mandatoryParts.toArray(new Rectangle[0]));
    }

}
