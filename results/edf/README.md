# High-Level Results about Earliest-Deadline First (EDF) Scheduling

This folder collects the main theorems in Prosa about EDF-scheduled systems. There are currently the following results available.

## EDF Optimality

As a case study, Prosa includes the proof that EDF is optimal w.r.t. meeting deadlines on an ideal uniprocessor. 

**EDF optimality** on ideal uniprocessors: [optimality.v](optimality.v). 

## Response-Time Bounds

On the more practical side, Prosa includes several **response-time bounds** for EDF. The proofs of these RTAs are based on abstract RTA.

The following RTAs all assume ideal uniprocessors and the basic Liu & Layland readiness model (i.e., jobs exhibit neither release jitter nor self-suspensions), but work for arbitrary arrival curves and arbitrary deadlines.

### (1) EDF RTA with Bounded Priority Inversions

The main result in [rta/bounded_pi.v](rta/bounded_pi.v) provides a general response-time bound assuming a bound on priority inversion (for whatever reason) is known.

### (2) EDF RTA with Bounded Non-Preemptive Segments

The main theorem in [rta/bounded_nps.v](rta/bounded_nps.v) provides a refinement of (1) based on the more specific assumption that priority inversions are caused by lower-priority non-preemptive jobs with bounded non-preemptive segment lengths. 

### (3) EDF RTA for Fully Preemptive Jobs

The RTA provided in [rta/fully_preemptive.v](rta/fully_preemptive.v) applies (2) to the commonly assumed case of fully preemptive tasks (i.e., the complete absence of non-preemptive segments), which matches the classic Liu & Layland model. 

### (4) EDF RTA for Fully Non-Preemptive Jobs

The file [rta/fully_nonpreemptive.v](rta/fully_nonpreemptive.v) provides a refinement of (2) for the case in which each job forms a single non-preemptive segment, i.e., where in-progress jobs execute with run-to-completion semantics and cannot be preempted at all.

### (5) EDF RTA for Floating Non-Preemptive Sections

The file [rta/floating_nonpreemptive.v](rta/floating_nonpreemptive.v) provides an RTA based on (2) for tasks that execute mostly preemptively, but that may also exhibit some non-preemptive segments (of bounded length) at unpredictable times. 

### (6) EDF RTA for Limited-Preemptive Tasks

The file [rta/limited_preemptive.v](rta/limited_preemptive.v) provides an RTA based on (2) for tasks that consist of a sequence of non-preemptive segments, separated by fixed preemption points. 

