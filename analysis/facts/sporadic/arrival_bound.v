Require Import prosa.util.all.
Require Export prosa.model.task.arrival.sporadic.
Require Export prosa.analysis.facts.model.task_arrivals.

(** * Sporadic Arrival Bound *)

(** In the following, we upper bound the number of jobs that can
    arrive in any interval as constrained by the sporadic task model's
    minimum inter-arrival time [task_min_inter_arrival_time]. *)
Section SporadicArrivalBound.

  (** Consider any sporadic tasks  ... *)
  Context {Task : TaskType} `{SporadicModel Task}.

  (** ... and their jobs. *)
  Context {Job : JobType} `{JobTask Job Task} `{JobArrival Job}.

  (** We define the classic "ceiling of the interval length divided by
      minimum inter-arrival time", which we prove to be correct in the
      following. *)
  Definition max_sporadic_arrivals (tsk : Task) (delta : duration) :=
    div_ceil delta (task_min_inter_arrival_time tsk).

  (** To establish the bound's soundness, consider any well-formed
      arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_valid_arrival_sequence : valid_arrival_sequence arr_seq.

  (** ... and any valid sporadic task [tsk] to be analyzed. *)
  Variable tsk : Task.
  Hypothesis H_sporadic_model: respects_sporadic_task_model arr_seq tsk.
  Hypothesis H_valid_inter_min_arrival: valid_task_min_inter_arrival_time tsk.

  (** Before we can establish the bound, we require two auxiliary
      bounds, which we derive next. First, we consider minimum offset
      of the <<n-th>> job of the task that arrives in a given interval. *)
  Section NthJob.

    (** For technical reasons, we require a "dummy" job in scope to
        use the [nth] function. In the proofs, we establish that the
        [dummy] job is never used, i.e., it is an irrelevant artifact
        induced by the ssreflect API. It may be safely ignored. *)
    Variable dummy : Job.

    (** We observe that the <<i-th>> job to arrive in an interval <<[t1,t2)>>
        arrives no earlier than [(task_min_inter_arrival_time tsk) *i]
        time units after the beginning of the interval due the minimum
        inter-arrival time of the sporadic task. *)
    Lemma arrival_of_nth_job :
      forall t1 t2 n i j,
        n = number_of_task_arrivals arr_seq tsk t1 t2 ->
        i < n ->
        j = nth dummy (task_arrivals_between arr_seq tsk t1 t2) i ->
        job_arrival j >= t1 + (task_min_inter_arrival_time tsk) * i.
    Proof.
      move=> t1 t2 n i j. rewrite /number_of_task_arrivals.
      case ARR : (task_arrivals_between arr_seq tsk t1 t2) => [|j' js'] -> // LIM JOB.
      elim: i LIM j JOB => [LIM j JOB|i IH LIM j JOB].
      { rewrite muln0 addn0.
        apply: job_arrival_between_ge => //.
        apply: (task_arrivals_between_subset _ tsk _ t2).
        by rewrite JOB ARR; apply mem_nth. }
      { rewrite mulnSr addnA.
        pose prev_j := nth dummy (j' :: js') i.
        have prev_LIM : t1 + task_min_inter_arrival_time tsk * i + task_min_inter_arrival_time tsk
                        <= job_arrival prev_j + task_min_inter_arrival_time tsk
          by rewrite leq_add2r; apply IH => //; lia.
        apply: (leq_trans prev_LIM).
        have IN_j : j \in task_arrivals_between arr_seq tsk t1 t2
          by rewrite JOB ARR; apply mem_nth.
        have IN_prev : prev_j \in task_arrivals_between arr_seq tsk t1 t2
          by rewrite /prev_j ARR; apply mem_nth; lia.
        apply: H_sporadic_model => //=.
        { rewrite JOB /prev_j  => /eqP.
          rewrite nth_uniq; try lia; rewrite -ARR.
          by apply: task_arrivals_between_uniq. }
        { by apply/in_arrivals_implies_arrived/(task_arrivals_between_subset _ tsk t1 t2). }
        { by apply/in_arrivals_implies_arrived/(task_arrivals_between_subset _ tsk t1 t2). }
        { apply: in_task_arrivals_between_implies_job_of_task.
          exact IN_prev. }
        { apply: in_task_arrivals_between_implies_job_of_task.
          exact: IN_j. }
        { rewrite /prev_j JOB.
          have SORTED : sorted by_arrival_times (j' :: js')
            by rewrite -ARR; apply task_arrivals_between_sorted.
          eapply (sorted_leq_nth _ _ _ SORTED); try lia.
          - rewrite unfold_in simpl_predE; lia.
          - rewrite unfold_in simpl_predE; lia. } }
      Unshelve. all: by rewrite /by_arrival_times/transitive/reflexive; lia.
    Qed.

  End NthJob.

  (** As a second auxiliary lemma, we establish a minimum length on
      the interval for a given number of arrivals by applying the
      previous lemma to the last job in the interval. We consider only
      the case of "many" jobs, i.e., [n >= 2], which ensures that the
      interval <<[t1, t2)>> spans at least one inter-arrival time. *)
  Lemma minimum_distance_for_n_sporadic_arrivals:
    forall t1 t2 n,
      number_of_task_arrivals arr_seq tsk t1 t2 = n ->
      n >= 2 ->
      t2 > t1 + (task_min_inter_arrival_time tsk) * n.-1.
  Proof.
    move=> t1 t2 n H_num_arrivals H_many_jobs.
    (* First, let us get ourselves a job so we can discharge the dummy job parameter. *)
    destruct (task_arrivals_between arr_seq tsk t1 t2) as [|j js] eqn:ARR;
      first by move: ARR H_num_arrivals H_many_jobs; rewrite /number_of_task_arrivals => -> //= ->; lia.
    (* Now that we can use [nth], let's proceed with the actual proof. *)
    set j_last := (nth j (task_arrivals_between arr_seq tsk t1 t2) n.-1).
    have LAST : job_arrival j_last  < t2.
    { apply: job_arrival_between_lt => //.
      apply: task_arrivals_between_subset.
      apply mem_nth.
      by move: H_num_arrivals; rewrite /number_of_task_arrivals => ->; lia. }
    have DIST :  t1 + task_min_inter_arrival_time tsk * n.-1 <= job_arrival j_last.
    { apply: arrival_of_nth_job; auto;
        first by rewrite [number_of_task_arrivals arr_seq tsk t1 _]H_num_arrivals; lia.
      by []. }
    lia.
  Qed.

  (** Based on the above lemma, it is easy to see that
      [max_sporadic_arrivals] is indeed a correct upper bound on the
      maximum number of arrivals in a given interval. *)
  Theorem sporadic_task_arrivals_bound:
    forall t1 t2,
      number_of_task_arrivals arr_seq tsk t1 t2 <= max_sporadic_arrivals tsk (t2 - t1).
  Proof.
    move=> t1 t2.
    case COUNT: (number_of_task_arrivals arr_seq tsk t1 t2) => // [n'].
    case COUNT: n' COUNT => // [|n] NARR.
    { (* one arrival *)
      apply div_ceil_gt0 => //; rewrite subn_gt0.
      by eapply number_of_task_arrivals_nonzero; eauto. }
    { (* two or more arrivals *)
      clear n' COUNT.
      move: NARR. set n' := n.+2 => NARR.
      have SEP: t2 >  t1 + (task_min_inter_arrival_time tsk) * n'.-1
        by apply: minimum_distance_for_n_sporadic_arrivals.
      move: SEP. rewrite -ltn_subRL => SEP.
      by apply: div_ceil_multiple. }
  Qed.


End SporadicArrivalBound.
