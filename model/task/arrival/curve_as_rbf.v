Require Export prosa.util.all.
Require Export prosa.model.task.arrival.request_bound_functions.
Require Export prosa.model.task.arrival.curves.

(** * Converting an Arrival Curve + Worst-Case/Best-Case to a Request-Bound Function (RBF) *)

(** In the following, we show a way to convert a given arrival curve,
    paired with a worst-case/best-case execution time, to a request-bound function.
    Definitions and proofs will handle both lower-bounding and upper-bounding arrival
    curves. *)
Section ArrivalCurveToRBF.

  (** Consider any type of tasks with a given cost ... *)
  Context {Task : TaskType} `{TaskCost Task} `{TaskMinCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobCost Job}.

  (** Let [MaxArr] and [MinArr] represent two arrivals curves. [MaxArr] upper-bounds
      the possible number or arrivals for a given task, whereas [MinArr] lower-bounds it. *)
  Context `{MaxArr : MaxArrivals Task} `{MinArr : MinArrivals Task}.

  (** We define the conversion to a request-bound function as the product of the task cost and the
      number of arrivals during [Δ]. In the upper-bounding case, the cost of a task will represent
      the WCET of its jobs. Symmetrically, in the lower-bounding case, the cost of a task will
      represent the BCET of its jobs. *)
  Definition task_max_rbf (arrivals :  Task -> duration -> nat) task Δ := task_cost task * arrivals task Δ.
  Definition task_min_rbf (arrivals :  Task -> duration -> nat) task Δ := task_min_cost task * arrivals task Δ.

  (** Finally, we show that the newly defined functions are indeed request-bound functions. *)
  Global Program Instance MaxArrivalsRBF : MaxRequestBound Task := task_max_rbf max_arrivals.
  Global Program Instance MinArrivalsRBF : MinRequestBound Task := task_min_rbf min_arrivals.

  (** In the following section, we prove that the transformation yields a request-bound
      function that conserves correctness properties in both the upper-bounding
      and lower-bounding cases. *)
  Section Facts.

    (** First, we establish the validity of the transformation for a single, given task. *)
    Section SingleTask.

      (** Consider an arbitrary task [tsk] ... *)
      Variable tsk : Task.

      (** ... and any job arrival sequence. *)
      Variable arr_seq : arrival_sequence Job.

      (** First, note that any valid upper-bounding arrival curve, after being
          converted, is a valid request-bound function. *)
      Theorem valid_arrival_curve_to_max_rbf :
        forall (arrivals : Task -> duration -> nat),
          valid_arrival_curve (arrivals tsk) ->
          valid_request_bound_function ((task_max_rbf arrivals) tsk).
      Proof.
        move => ARR [ZERO MONO].
        split.
        - by rewrite /task_max_rbf ZERO muln0.
        - move => x y LEQ.
          rewrite /task_max_rbf.
          destruct (task_cost tsk); first by rewrite mul0n.
          by rewrite leq_pmul2l //; apply MONO.
      Qed.

      (** The same idea can be applied in the lower-bounding case. *)
      Theorem valid_arrival_curve_to_min_rbf :
        forall (arrivals : Task -> duration -> nat),
          valid_arrival_curve (arrivals tsk) ->
          valid_request_bound_function ((task_min_rbf arrivals) tsk).
      Proof.
        move => ARR [ZERO MONO].
        split.
        - by rewrite /task_min_rbf ZERO muln0.
        - move => x y LEQ.
          rewrite /task_min_rbf.
          destruct (task_min_cost tsk); first by rewrite mul0n.
          by rewrite leq_pmul2l //; apply MONO.
      Qed.

      (** Next, we prove that the task respects the request-bound function in
          the upper-bounding case. Note that, for this to work, we assume that the
          cost of tasks upper-bounds the cost of the jobs belonging to them (i.e.,
          the task cost is the worst-case). *)
      Theorem respects_arrival_curve_to_max_rbf :
        jobs_have_valid_job_costs ->
        respects_max_arrivals arr_seq tsk (MaxArr tsk) ->
        respects_max_request_bound arr_seq tsk ((task_max_rbf MaxArr) tsk).
      Proof.
        move=> TASK_COST RESPECT t1 t2 LEQ.
        specialize (RESPECT t1 t2 LEQ).
        apply leq_trans with (n := task_cost tsk * number_of_task_arrivals arr_seq tsk t1 t2) => //.
        - rewrite /max_arrivals /number_of_task_arrivals -sum1_size big_distrr //= muln1 leq_sum_seq // => j.
          rewrite mem_filter => /andP [/eqP TSK _] _.
          rewrite -TSK.
          by apply TASK_COST.
        - by destruct (task_cost tsk) eqn:C; rewrite /task_max_rbf C // leq_pmul2l.
      Qed.

      (** Finally, we prove that the task respects the request-bound function also in
          the lower-bounding case. This time, we assume that the cost of tasks lower-bounds
          the cost of the jobs belonging to them. (i.e., the task cost is the best-case). *)
      Theorem respects_arrival_curve_to_min_rbf :
        jobs_have_valid_min_job_costs ->
        respects_min_arrivals arr_seq tsk (MinArr tsk) ->
        respects_min_request_bound arr_seq tsk ((task_min_rbf MinArr) tsk).
      Proof.
        move=> TASK_COST RESPECT t1 t2 LEQ.
        specialize (RESPECT t1 t2 LEQ).
        apply leq_trans with (n := task_min_cost tsk * number_of_task_arrivals arr_seq tsk t1 t2) => //.
        - by destruct (task_min_cost tsk) eqn:C; rewrite /task_min_rbf C // leq_pmul2l.
        - rewrite /min_arrivals /number_of_task_arrivals -sum1_size big_distrr //= muln1 leq_sum_seq // => j.
          rewrite mem_filter => /andP [/eqP TSK _] _.
          rewrite -TSK.
          by apply TASK_COST.
      Qed.

    End SingleTask.

    (** Next, we lift the results to the previous section to an arbitrary task set. *)
    Section TaskSet.

      (** Let [ts] be an arbitrary task set... *)
      Variable ts : TaskSet Task.

      (** ... and consider any job arrival sequence. *)
      Variable arr_seq : arrival_sequence Job.

      (** First, we generalize the validity of the transformation to a task set both in
          the upper-bounding case ... *)
      Corollary valid_taskset_arrival_curve_to_max_rbf :
        valid_taskset_arrival_curve ts MaxArr ->
        valid_taskset_request_bound_function ts MaxArrivalsRBF.
      Proof.
        move=> VALID tsk IN.
        specialize (VALID tsk IN).
        by apply valid_arrival_curve_to_max_rbf.
      Qed.

      (** ... and in the lower-bounding case. *)
      Corollary valid_taskset_arrival_curve_to_min_rbf :
        valid_taskset_arrival_curve ts MinArr ->
        valid_taskset_request_bound_function ts MinArrivalsRBF.
      Proof.
        move=> VALID tsk IN.
        specialize (VALID tsk IN).
        by apply valid_arrival_curve_to_min_rbf.
      Qed.

      (** Second, we show that a task set that respects a given arrival curve also respects
          the produced request-bound function, lifting the result obtained in the single-task
          case. The result is valid in the upper-bounding case... *)
      Corollary taskset_respects_arrival_curve_to_max_rbf :
        jobs_have_valid_job_costs ->
        taskset_respects_max_arrivals arr_seq ts ->
        taskset_respects_max_request_bound arr_seq ts.
      Proof.
        move=> TASK_COST SET_RESPECTS tsk IN.
        by apply respects_arrival_curve_to_max_rbf, SET_RESPECTS.
      Qed.

      (** ...as well as in the lower-bounding case. *)
      Corollary taskset_respects_arrival_curve_to_min_rbf :
        jobs_have_valid_min_job_costs ->
        taskset_respects_min_arrivals arr_seq ts ->
        taskset_respects_min_request_bound arr_seq ts.
      Proof.
        move=> TASK_COST SET_RESPECTS tsk IN.
        by apply respects_arrival_curve_to_min_rbf, SET_RESPECTS.
      Qed.

    End TaskSet.

  End Facts.

End ArrivalCurveToRBF.

(** We add the lemmas into the "Hint Database" basic_rt_facts so that
    they become available for proof automation. *)
Global Hint Resolve
  valid_arrival_curve_to_max_rbf
  respects_arrival_curve_to_max_rbf
  valid_taskset_arrival_curve_to_max_rbf
  taskset_respects_arrival_curve_to_max_rbf
  : basic_rt_facts.
