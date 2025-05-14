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
import minicp.util.GraphUtil;
import minicp.util.GraphUtil.Graph;
import minicp.util.exception.InconsistencyException;
import minicp.util.exception.NotImplementedException;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Arc Consistent AllDifferent Constraint
 *
 * Algorithm described in
 * "A filtering algorithm for constraints of difference in CSPs" J-C. Régin, AAAI-94
 */
public class AllDifferentDC extends AbstractConstraint {

    private IntVar[] x;

    private final MaximumMatching maximumMatching;

    private final int nVar;
    private int nVal;

    // residual graph
    private ArrayList<Integer>[] in;
    private ArrayList<Integer>[] out;
    private int nNodes;
    protected Graph g = new Graph() {
        @Override
        public int n() {
            return nNodes;
        }

        @Override
        public Iterable<Integer> in(int idx) {
            return in[idx];
        }

        @Override
        public Iterable<Integer> out(int idx) {
            return out[idx];
        }
    };

    private int[] match;
    private boolean[] matched;

    private int minVal;
    private int maxVal;

    public AllDifferentDC(IntVar... x) {
        super(x[0].getSolver());
        this.x = x;
        maximumMatching = new MaximumMatching(x);
        match = new int[x.length];
        this.nVar = x.length;
    }

    @Override
    public void post() {
        for (int i = 0; i < nVar; i++) {
            x[i].propagateOnDomainChange(this);
        }
        updateRange();

        matched = new boolean[nVal];
        nNodes = nVar + nVal + 1;
        in = new ArrayList[nNodes];
        out = new ArrayList[nNodes];
        for (int i = 0; i < nNodes; i++) {
            in[i] = new ArrayList<>();
            out[i] = new ArrayList<>();
        }
        propagate();
    }

    private void updateRange() {
        minVal = Integer.MAX_VALUE;
        maxVal = Integer.MIN_VALUE;
        for (int i = 0; i < nVar; i++) {
            minVal = Math.min(minVal, x[i].min());
            maxVal = Math.max(maxVal, x[i].max());
        }
        nVal = maxVal - minVal + 1;
    }


    private void updateGraph() {
        nNodes = nVar + nVal + 1;
        int sink = nNodes - 1;
        for (int j = 0; j < nNodes; j++) {
            in[j].clear();
            out[j].clear();
        }
        // TODO continue the implementation for representing the residual graph

        for (int var = 0; var < nVar; var++) {
            int matchedVal = match[var];  // −1 if none

            // iterate over the current domain of x
            for (int a = x[var].min(); a <= x[var].max(); a++) {
                if (!x[var].contains(a)) continue;

                int valNode = nVar + (a - minVal);

                if (a == matchedVal) {    // matched edge
                    in[var].add(valNode);
                    out[valNode].add(var);
                } else {                  // unmatched edge
                    out[var].add(valNode);
                    in[valNode].add(var);
                }
            }
        }

        // sink arcs
        for (int off = 0; off < nVal; off++) {
            int valNode = nVar + off;
            if (matched[off]) {           // matched value
                out[sink].add(valNode);
                in[valNode].add(sink);
            } else {                      // free value
                out[valNode].add(sink);
                in[sink].add(valNode);
            }
        }
    }


    @Override
    public void propagate() {
        // TODO Implement the filtering
        // hint: use maximumMatching.compute(match) to update the maximum matching
        //       use updateRange() to update the range of values
        //       use updateGraph() to update the residual graph
        //       use  GraphUtil.stronglyConnectedComponents to compute SCC's

        // 1. refresh
        updateRange();

        // 2. compute a maximum matching
        Arrays.fill(match, -1);
        maximumMatching.compute(match);    // fills the array 'match'

        // 3. mark which values are matched
        matched = new boolean[nVal];
        for (int v : match)
            if (v >= 0) matched[v - minVal] = true;

        // 4. build the residual graph
        updateGraph();

        //5. compute strongly-connected components
        int[] scc = GraphUtil.stronglyConnectedComponents(g);

        //6. prune
        for (int var = 0; var < nVar; var++) {
            for (int a = x[var].min(); a <= x[var].max(); a++) {
                if (!x[var].contains(a)) continue;
                if (a == match[var]) continue;     // keep matched value

                int valNode = nVar + (a - minVal);
                if (scc[var] != scc[valNode]) {
                    x[var].remove(a);            // unsupported value
                }
            }
        }
    }
}
