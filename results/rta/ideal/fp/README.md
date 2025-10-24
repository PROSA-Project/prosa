# RTAs for Fixed-Priority Scheduling on Ideal Uniprocessors

The following analyses all and assume the basic Liu & Layland readiness model (i.e., jobs exhibit neither release jitter nor self-suspensions) and work for arbitrary arrival curves and arbitrary deadlines.


### (1) FP RTA with Bounded Priority Inversions

The generic result in [`bounded_pi`](./bounded_pi.v) provides a general response-time bound assuming a bound on priority inversion (for whatever reason) is known.

### (2) FP RTA with Bounded Non-Preemptive Segments

The main theorem in [`bounded_nps`](./bounded_nps.v) provides a refinement of (1) based on the more specific assumption that priority inversions are caused by lower-priority non-preemptive jobs with bounded non-preemptive segment lengths. 

### (3) FP RTA for Fully Preemptive Jobs

The RTA provided in [`fully_preemptive`](./fully_preemptive.v) applies (2) to the common case of fully preemptive tasks (i.e., the complete absence of non-preemptive segments), which matches the classic Liu & Layland model. 

### (4) FP RTA for Fully Non-Preemptive Jobs

The RTA in [`fully_nonpreemptive`](./fully_nonpreemptive.v) provides a refinement of (2) for the case in which each job forms a single non-preemptive segment, i.e., where in-progress jobs execute with run-to-completion semantics and cannot be preempted at all.

### (5) FP RTA for Floating Non-Preemptive Sections

The RTA in [`floating_nonpreemptive`](./floating_nonpreemptive.v) provides an RTA based on (2) for tasks that execute mostly preemptively, but that may also exhibit some non-preemptive segments (of bounded length) at unpredictable times. 

### (6) FP RTA for Limited-Preemptive Tasks

The RTA in [`limited_preemptive`](./limited_preemptive.v) provides an RTA based on (2) for tasks that consist of a sequence of non-preemptive segments, separated by fixed preemption points. 

### (7) FP RTA for Fully Preemptive Jobs with Computed Fixpoints

The RTA provided in [`comp.fully_preemptive`](./comp/fully_preemptive.v) is a refinement of (3), in which the fixpoints upon which the analysis rests are assumed to have been computed with the functions provided in [`prosa.util.fixpoint`](../../../../util/fixpoint.v). See the comment at the start of the file for further explanation. 

### (8) FP RTA for Non-Sequential Tasks with Bounded Priority Inversions 

The result in [`nonseq.bounded_pi`](nonseq/bounded_pi.v) provides an alternative to (1) under the relaxed assumption that tasks may not be sequential, i.e., the jobs of a given task don't necessarily have to execute in the order of their arrival times.



