package minicp.examples;

import minicp.util.io.InputReader;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.function.Supplier;

import java.util.Arrays;
import java.util.Random;
import java.util.stream.IntStream;
import minicp.engine.core.*;
import static minicp.cp.Factory.*;
import static minicp.cp.BranchingScheme.*;
import minicp.search.DFSearch;
import minicp.search.SearchStatistics;
import minicp.util.exception.InconsistencyException;
import minicp.util.io.InputReader;
import java.util.*;
import minicp.engine.constraints.Absolute;
import minicp.search.Objective;
import minicp.util.Procedure;


public class AircraftLanding {
    /* ‑‑ configuration flags ‑‑ */
    private static final boolean VERBOSE   = false;      // global on/off switch
    private static final int     LOG_EVERY = 1_000;     // local‑search iterations to skip between logs
    private static final long    CPU_LIMIT = 175_000_000_000L;   // 175 s (safety)
    private static final java.lang.management.ThreadMXBean TMX =
            java.lang.management.ManagementFactory.getThreadMXBean();

    private static final long t0 = System.nanoTime();
    private static void log(String fmt, Object... args) {
        if (!VERBOSE) return;
        double ms = (System.nanoTime() - t0) / 1e6;
        System.out.printf("[%8.1f ms] ", ms);
        System.out.printf(fmt + "%n", args);
    }
    private static long cpuNow() { return TMX.getCurrentThreadCpuTime(); }

    // ------------------------------------------------------------------

    /**
     * Main function that provides a solution to an instance
     *
     * @param instance instance to solve
     * @return best solution found to the instance
     */
    public static AircraftLandingSolution solve(AircraftLandingInstance instance) {
        log("====  solve() called  | planes=%d lanes=%d  ====", instance.nPlanes, instance.nLanes);

        int n = instance.nPlanes;
        int m = instance.nLanes;
        Plane[] P = instance.planes;

        Solver cp = makeSolver();

        IntVar[] time = makeIntVarArray(n, i -> makeIntVar(cp, 0, P[i].deadline));
        IntVar[] lane = makeIntVarArray(cp, n, m);

        IntVar[] cost = new IntVar[n];
        for (int i = 0; i < n; i++) {
            cost[i] = makeIntVar(cp, 0, P[i].deadline);
            cp.post(new Absolute(minus(time[i], P[i].wantedTime), cost[i]));
        }

        for (int i = 0; i < n; i++)
            for (int j = i + 1; j < n; j++) {
                int sepIJ = instance.switchDelay[P[i].type][P[j].type];
                int sepJI = instance.switchDelay[P[j].type][P[i].type];
                cp.post(new Separation(lane[i], lane[j], time[i], time[j], sepIJ, sepJI));
            }

        Objective obj = cp.minimize(sum(cost));

        DFSearch dfs = makeDfs(cp,
                and(firstFail(time), firstFail(lane))
        );

        final int[] bestT = new int[n];
        final int[] bestR = new int[n];
        dfs.onSolution(() -> {
            for (int i = 0; i < n; i++) {
                bestT[i] = time[i].min();
                bestR[i] = lane[i].min();
            }
        });

        dfs.optimize(obj);

        AircraftLandingSolution sol = new AircraftLandingSolution(instance);
        for (int i = 0; i < n; i++) {
            sol.landPlane(i, bestR[i], bestT[i]);
        }
        return sol;
    }
    /* helper used by local tweaks */
    private static boolean isGloballyFeasible(int[] time, Plane[] planes, AircraftLandingInstance ins) {
        int n = planes.length;
        for (int i = 0; i < n; i++) if (time[i] != -1)
            for (int j = 0; j < n; j++) if (time[j] != -1 && time[i] < time[j]) {
                int sep = ins.switchDelay[ planes[i].type ][ planes[j].type ];
                if (time[j] - time[i] < sep) return false;
            }
        return true;
    }
    /**
     * Function that list all feasible solutions to an instance.
     * <p>
     * This function does not count in the grade, and should only be used for debugging purposes, to verify that you
     * find all solutions to a (small) instance.
     * <p>
     * Even though it is not mandatory, it is STRONGLY ADVISED to implement it and pass the related tests :-) .
     * @param ins instance to solve
     * @return all feasible solutions found to the instance
     */
    public List<AircraftLandingSolution> findAll(AircraftLandingInstance ins) {
        log("Exhaustive enumeration launched (n=%d)", ins.nPlanes);
        int n = ins.nPlanes, m = ins.nLanes; Plane[] P = ins.planes;
        Solver cp = makeSolver();

        IntVar[] lane = makeIntVarArray(cp, n, m);
        IntVar[] time = IntStream.range(0, n)
                .mapToObj(i -> makeIntVar(cp, 0, P[i].deadline))
                .toArray(IntVar[]::new);

        IntVar[] absCost = new IntVar[n];
        for (int i = 0; i < n; i++) {
            absCost[i] = makeIntVar(cp, 0, P[i].deadline);          // upper bound is safe
            IntVar diff = plus(time[i], -P[i].wantedTime);   // diff = time[i] - wantedTime
            cp.post(new Absolute(diff, absCost[i]));
        }
        IntVar totalCost = sum(absCost);                // |t-wanted|
        Objective obj    = cp.minimize(totalCost);      // we will give this to DFS

        // pairwise separation constraints
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
            int sepIJ = ins.switchDelay[P[i].type][P[j].type];
            int sepJI = ins.switchDelay[P[j].type][P[i].type];
            cp.post(new Separation(lane[i], lane[j], time[i], time[j], sepIJ, sepJI));
        }

        DFSearch dfs = new DFSearch(cp.getStateManager(), () -> {
            IntVar best = null; int bestSize = Integer.MAX_VALUE;
            for (IntVar v : time) if (v.size() > 1 && v.size() < bestSize){best = v; bestSize = v.size();}
            for (IntVar v : lane) if (v.size() > 1 && v.size() < bestSize){best = v; bestSize = v.size();}
            if (best == null) return new minicp.util.Procedure[0];
            int val = best.min();
            IntVar v = best; // effectively final
            return new minicp.util.Procedure[]{() -> v.fix(val), () -> v.remove(val)};
        });

        List<AircraftLandingSolution> out = new ArrayList<>();
        dfs.onSolution(() -> {
            AircraftLandingSolution s = new AircraftLandingSolution(ins);
            for (int i = 0; i < n; i++) s.landPlane(i, lane[i].min(), time[i].min());
            try { s.compute(); out.add(s); } catch (RuntimeException ignored) {}
        });

        SearchStatistics st = dfs.solve();
        log("Enumeration finished – nodes=%d solutions=%d", st.numberOfNodes(), st.numberOfSolutions());
        return out;
    }
    /* constraint class for separation*/
    private static class Separation extends AbstractConstraint {
        private final IntVar li, lj;   // lane vars for i and j
        private final IntVar ti, tj;   // time vars for i and j
        private final int sepIJ, sepJI;

        Separation(IntVar li, IntVar lj, IntVar ti, IntVar tj,
                   int sepIJ, int sepJI) {
            super(li.getSolver());
            this.li = li; this.lj = lj;
            this.ti = ti; this.tj = tj;
            this.sepIJ = sepIJ; this.sepJI = sepJI;
        }

        @Override public void post() {
            // Wake when lanes get bound or times get tighter
            li.propagateOnBoundChange(this);
            lj.propagateOnBoundChange(this);
            ti.propagateOnBoundChange(this);
            tj.propagateOnBoundChange(this);
            propagate();
        }

        @Override public void propagate() throws InconsistencyException {
            // If lanes are already proven different, nothing to do.
            if (li.max() < lj.min() || lj.max() < li.min())
                return; // cannot be equal, separation irrelevant

            // If both lanes are fixed and equal, we must enforce precedence timings
            if (li.isFixed() && lj.isFixed() && li.min() == lj.min()
                    && ti.isFixed() && tj.isFixed()) {
                int d = tj.min() - ti.min();
                if (d >= 0) {
                    if (d < sepIJ) throw new InconsistencyException();
                } else {
                    if (-d < sepJI) throw new InconsistencyException();
                }
            }
        }
    }

    private static void backtrack(int k,
                                  Integer[] order,
                                  AircraftLandingInstance instance,
                                  int[] times,
                                  int[] lanes,
                                  List<AircraftLandingSolution> out) {

        int n = instance.nPlanes, m = instance.nLanes;

        if (k == n) {                                   // full schedule
            out.add(deepCopy(instance, times, lanes));
            return;
        }
        int pid = order[k];
        Plane p = instance.planes[pid];

        for (int l = 0; l < m; l++) {
            /* earliest feasible w.r.t. planes already on lane l */
            int last = -1, lastType = -1;
            for (int q = 0; q < n; q++)
                if (lanes[q] == l && (last == -1 || times[q] > times[last])) last = q;
            if (last != -1) lastType = instance.planes[last].type;

            int earliest = (last == -1) ? 0
                    : times[last] + instance.switchDelay[lastType][p.type];

            for (int t = earliest; t <= p.deadline; t++) {
                times[pid] = t; lanes[pid] = l;
                if (respectsLaneSeparation(times, lanes, instance))
                    backtrack(k + 1, order, instance, times, lanes, out);
                times[pid] = -1; lanes[pid] = -1;
            }
        }
    }

    /* cost of a complete schedule ------------------------------------------- */
    private static int scheduleCost(int[] times, AircraftLandingInstance ins) {
        int cost = 0;
        for (int i = 0; i < times.length; i++)
            cost += Math.abs(ins.planes[i].wantedTime - times[i]);
        return cost;
    }

    /* checks separation on every runway ------------------------------------- */
    private static boolean respectsLaneSeparation(int[] times,
                                                  int[] lane,
                                                  AircraftLandingInstance ins) {
        int n = times.length;
        for (int i = 0; i < n; i++) if (times[i] >= 0)
            for (int j = 0; j < n; j++) if (lane[i] == lane[j] && times[j] > times[i]) {
                int sep = ins.switchDelay[ins.planes[i].type][ins.planes[j].type];
                if (times[j] - times[i] < sep) return false;
            }
        return true;
    }

    /* deep copy used by enumeration ----------------------------------------- */
    private static AircraftLandingSolution deepCopy(AircraftLandingInstance instance,
                                                    int[] times,
                                                    int[] lane) {
        AircraftLandingSolution s = new AircraftLandingSolution(instance);
        for (int i = 0; i < times.length; i++)
            if (times[i] >= 0) s.landPlane(i, lane[i], times[i]);
        return s;
    }

    /**
     * A plane in the problem
     */
    public static class Plane {
        public int wantedTime;
        public int deadline;
        public int type;

        public Plane(int wantedTime, int deadline, int type) {
            this.type = type;
            this.wantedTime = wantedTime;
            this.deadline = deadline;
        }
    }

    /**
     * An instance of the aircraft landing problem
     */
    public static class AircraftLandingInstance {

        public int nPlanes, nTypes, nLanes;
        public Plane[] planes;
        public int[][] switchDelay;

        public AircraftLandingInstance(String url) {

            InputReader reader = new InputReader(url);

            nPlanes = reader.getInt();
            nTypes = reader.getInt();
            nLanes = reader.getInt();
            planes = new Plane[nPlanes];

            for (int i = 0; i < nPlanes; i++) {
                Plane plane = new Plane(reader.getInt(), reader.getInt(), reader.getInt());
                this.planes[i] = plane;
            }

            switchDelay = new int[nTypes][nTypes];
            for (int i = 0; i < nTypes; i++) {
                for (int j = 0; j < nTypes; j++) {
                    switchDelay[i][j] = reader.getInt();
                }
            }
        }

        public Plane getPlane(int i) {
            return planes[i];
        }

        /**
         * Gives the switch delay between two planes
         *
         * @param p1 first plane
         * @param p2 second plane
         * @return
         */
        public int switchDelay(Plane p1, Plane p2) {
            return switchDelay[p1.type][p2.type];
        }
    }

    /**
     * A solution to an aircraft landing instance.
     * <p>
     * Each time a plane lands, it must be declared using {@link AircraftLandingSolution#landPlane(int, int, int)}.
     * Once all planes are landed, {@link AircraftLandingSolution#compute()} and {@link AircraftLandingSolution#toString()} can be safely used.
     * A solution may be reset using {@link AircraftLandingSolution#clear()}.
     * <p>
     * DO NOT MODIFY THIS CLASS.
     */
    public static class AircraftLandingSolution {
        public AircraftLandingInstance instance;
        public List<Integer>[] lanes; // for each plane, the ids of the planes that have landed there
        public int[] times; // for each plane, the time at which it lands

        public AircraftLandingSolution(AircraftLandingInstance instance) {
            this.instance = instance;
            lanes = new ArrayList[instance.nLanes];
            for (int i = 0; i < lanes.length; i++) {
                lanes[i] = new ArrayList<>();
            }
            times = new int[instance.nPlanes];
        }

        /**
         * Encodes the landing of a plane in a solution.
         * This does not verify any constraint (checking is only done in {@link AircraftLandingSolution#compute()})
         *
         * @param planeId if of the plane to land
         * @param lane    lane on which the plane is landing
         * @param time    time at which the plane is landing
         */
        public void landPlane(int planeId, int lane, int time) {
            lanes[lane].add(planeId);
            times[planeId] = time;
        }

        /**
         * Resets this solution, so that this object can encode a new one
         */
        public void clear() {
            for (int i = 0; i < lanes.length; i++) {
                lanes[i].clear();
            }
        }

        /**
         * Gives the cost of a solution and throws a {@link RuntimeException} if the solution is invalid
         *
         * @return solution cost
         */
        public int compute() {
            int cost = 0;
            // sort each lane content based on the landing time of the planes, to have the planes in order of arrival
            for (List<Integer> lane : lanes) {
                lane.sort(Comparator.comparingInt(plane -> times[plane]));
            }
            // tracks the planes that have been seen
            HashSet<Integer> seen = new HashSet<>();
            for (List<Integer> lane : lanes) {
                int prev = -1;
                for (int current : lane) {
                    Plane plane = instance.getPlane(current);
                    if (times[current] < 0 || times[current] > plane.deadline) {
                        throw new RuntimeException("Time of plane " + current + " is out of the time window : " + times[current] + " not in [0," + plane.deadline + "]");
                    }
                    if (prev != -1) {
                        // check if transition between prev and current is has enough delay
                        Plane previousPlane = instance.getPlane(prev);
                        int switchDelay = instance.switchDelay(previousPlane, plane);
                        if (times[prev] + switchDelay > times[current]) {
                            throw new RuntimeException("Plane " + prev + " and plane " + current + " are too close to one another.\n" + "Expected minimum delay was " + switchDelay + " but got " + (times[prev] - times[current]));
                        }
                    }
                    cost += Math.abs(plane.wantedTime - times[current]);
                    prev = current;
                    if (seen.contains(current)) throw new RuntimeException("Plane " + current + " landed more than once");
                    seen.add(current);
                }
            }
            if (seen.size() != instance.nPlanes) {
                throw new RuntimeException("Some planes did not land");
            }
            return cost;
        }


        @Override
        public String toString() {
            StringBuilder b = new StringBuilder();
            b.append("Cost: ");
            b.append(compute());
            b.append("\n");
            for (List<Integer> lane : lanes) {
                b.append("- ");
                for (int i = 0; i < lane.size(); i++) {
                    int planeId = lane.get(i);
                    b.append(planeId);
                    b.append("(t=");
                    b.append(times[planeId]);
                    b.append(')');
                    if (i < lane.size() - 1) b.append(", ");
                }
                b.append("\n");
            }
            return b.toString();
        }
    }


    public static void main(String[] args) {
        //TODO change file to test the various instances.
//        AircraftLandingInstance instance = new AircraftLandingInstance("data/alp/training");
        if (args.length != 1) {
            System.err.println("Usage: java … AircraftLanding <instance-file>");
            System.exit(1);
        }
        AircraftLandingInstance instance = new AircraftLandingInstance(args[0]);
        AircraftLanding alp = new AircraftLanding();
        AircraftLandingSolution solution = alp.solve(instance);
        System.out.println(solution);
    }
}
