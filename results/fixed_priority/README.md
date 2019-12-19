# High-Level Results about Fixed-Priority (FP) Scheduling

This folder collects the main theorems in Prosa about FP-scheduled systems. There are currently the following results available.


## Response-Time Bounds

Prosa includes several **response-time bounds** for FP scheduling. The proofs of these RTAs are based on abstract RTA.

### (1) FP RTA with Bounded Priority Inversions

The main result in [rta/bounded_pi.v](rta/bounded_pi.v) provides a general response-time bound assuming a bound on priority inversion (for whatever reason) is known.

### (2) FP RTA with Bounded Non-Preemptive Segments

The main theorem in [rta/bounded_nps.v](rta/bounded_nps.v) provides a refinement of (1) based on the more specific assumption that priority inversions are caused by lower-priority non-preemptive jobs with bounded non-preemptive segment lengths. 

### (3) FP RTA for Fully Preemptive Jobs

The RTA provided in [rta/fully_preemptive.v](rta/fully_preemptive.v) applies (2) to the commonly assumed case of fully preemptive tasks (i.e., the complete absence of non-preemptive segments), which matches the classic Liu & Layland model. 

### (4) FP RTA for Fully Non-Preemptive Jobs

The file [rta/fully_nonpreemptive.v](rta/fully_nonpreemptive.v) provides a refinement of (2) for the case in which each job forms a single non-preemptive segment, i.e., where in-progress jobs execute with run-to-completion semantics and cannot be preempted at all.

### (5) FP RTA for Floating Non-Preemptive Sections

The file [rta/floating_nonpreemptive.v](rta/floating_nonpreemptive.v) provides an RTA based on (2) for tasks that execute mostly preemptively, but that may also exhibit some non-preemptive segments (of bounded length) at unpredictable times. 

### (6) FP RTA for Limited-Preemptive Tasks

The file [rta/limited_preemptive.v](rta/limited_preemptive.v) provides an RTA based on (2) for tasks that consist of a sequence of non-preemptive segments, separated by fixed preemption points. 

