
(* TODO: optimize imports *)
Require Export prosa.util.all.
Require Export prosa.analysis.facts.model.rbf.
Require Export prosa.analysis.facts.busy_interval.ideal.busy_interval.
Require Export prosa.analysis.facts.model.task_arrivals.
Require Export prosa.analysis.facts.model.sequential.
Require Export prosa.model.schedule.work_conserving.
Require Export prosa.model.readiness.basic.
Require Export prosa.results.fixed_priority.rta.bounded_pi.
Require Export prosa.model.priority.numeric_fixed_priority.
Require Export prosa.analysis.facts.readiness.basic.
Require Export prosa.model.task.preemption.fully_preemptive.
Require Export prosa.results.fixed_priority.rta.bounded_nps.
Require Export prosa.analysis.facts.preemption.task.preemptive.
Require Export prosa.analysis.facts.preemption.rtc_threshold.preemptive.
(* Require Export prosa.analysis.shared_resources.definitions. *)
(* Require Export prosa.analysis.shared_resources.properties. *)


(* ---------------------------------------------------------------------- *)
(* -------------------------------- MOVE -------------------------------- *)
(* ---------------------------------------------------------------------- *)

(* TODO: move *)
Lemma pos_max_implies_exists :
  forall {T : Type} (xs : seq T) (P : pred T) (F : T -> nat),
    0 < \max_(x <- xs | P x) F x ->
    exists x0, (P x0) /\ 0 < F x0.
Proof.
  clear; move => T xs P F; elim: xs; first by rewrite big_nil.
  move => x xs IHxs MAX.
  rewrite big_cons in MAX.
  destruct (P x) eqn: Px.
  { move: MAX. rewrite -addn1.
    rewrite leq_max => /orP [GE|GE].
    exists x. by done.
    rewrite addn1 in GE.
    apply IHxs in GE.
    by rewrite addn1.
  }
  { by apply IHxs. }
Qed.



(* ---------------------------------------------------------------------- *)
(* -------------------------------- MAIN -------------------------------- *)
(* ---------------------------------------------------------------------- *)


(* ----------------------------- Definitions ---------------------------- *)


  (** TODO: name *)
  Section Locks.

    Context {Task : TaskType}.
    Context `{TaskCost Task}.

    Context `{TaskPriority Task}.

    Context {Job : JobType}.
    Context `{JobTask Job Task}.
    Context `{JobArrival Job}.
    Context `{JobCost Job}.

    (* TODO: comment *)
    Context {Resource : eqType}.

    (* *)
    Class JobResources (Job : JobType) :=
      job_needs : Job -> work -> seq Resource.

    Context `{JobResources Job}.

    Definition is_locked (j : Job) (r : Resource) (w : work) :=
      r \in job_needs j w.

    Definition acquired (j : Job) (r : Resource) (w : work) :=
      (is_locked j r w) && ((w > 0) ==> ~~ (is_locked j r w.-1)).

    Definition released (j : Job) (r : Resource) (w : work) :=
      (w > 0) && (is_locked j r w.-1) && ((w < job_cost j) ==> ~~ (is_locked j r w)).

    Definition resources (j : Job) :=
      undup (flatten [seq (job_needs j w) | w <- iota 0 (job_cost j)]).

    Structure CriticalSection :=
      build_cs
        { cs_job : Job
        ; cs_resource : Resource
        ; cs_start : work
        ; cs_end : work
        }.

    (** To make it compatible with ssreflect, we define a decidable
        equality for critical section. *)
    Definition cs_eqdef (cs1 cs2 : CriticalSection) :=
      (cs_job cs1 == cs_job cs2)
      && (cs_resource cs1 == cs_resource cs2)
      && (cs_start cs1 == cs_start cs2)
      && (cs_end cs1 == cs_end cs2).

    (** Next, we prove that [cs_eqdef] is indeed an equality, ... *)
    Lemma eqn_cs : Equality.axiom cs_eqdef.
    Proof.
      unfold Equality.axiom; intros x y.
      destruct (cs_eqdef x y) eqn:EQ.
      { apply ReflectT.
        move: EQ => /andP [/andP [/andP [/eqP JOB /eqP RES] /eqP ST] /eqP EN].
        by destruct x, y; simpl in *; subst. }
      { apply ReflectF.
        unfold cs_eqdef, not in * => BUG.
        apply negbT in EQ.
        repeat rewrite negb_and in EQ.
        destruct x, y.
        move: BUG => [JOB RES ST EN].
        rewrite JOB RES ST EN //= in EQ.
        by subst; rewrite !eq_refl in EQ.
      }
    Defined.

    (** ..., which allows instantiating the canonical structure for [[eqType of CriticalSection]]. *)
    Canonical cs_eqMixin := EqMixin eqn_cs.
    Canonical cs_eqType := Eval hnf in EqType CriticalSection cs_eqMixin.

    Definition job_critical_sections (j : Job) :=
      let all_combinations :=
        allpairs pair (resources j) (allpairs pair (iota 0 (job_cost j)) (iota 0 (job_cost j).+1)) in
      let is_correct '(r, (t1, t2)) :=
        (acquired j r t1) && (released j r t2) && (all (is_locked j r) (index_iota t1 t2)) in
      let filtered :=
        filter is_correct all_combinations in
      map (fun '(r, (t1, t2)) => build_cs j r t1 t2) filtered.


  End Locks.

  Section Tests.

    Context {Task : TaskType}.

    Context {Job : JobType}.
    Context `{JobTask Job Task}.
    Context `{JobArrival Job}.

    #[global,program] Instance JobCost : JobCost Job := fun _ => 3.
    Let Resource := [eqType of nat].

    Variable j : Job.
    
    
    #[global,program] Instance JobResources2 : @JobResources Resource Job :=
      fun _ w =>
        match w with
        | 0 => [::0]
        | 1 => [::0; 1]
        | 2 => [::0; 1]
        | _ => [::]
        end.

    Compute (job_critical_sections j).
    (* ==> [:: {| cs_job := j; cs_resource := 0; cs_start := 0; cs_end := 3 |};
              {| cs_job := j; cs_resource := 1; cs_start := 1; cs_end := 3 |}]
     *)



    
    #[local] Existing Instance NumericFPAscending.
    #[local] Existing Instance fully_preemptive_job_model.
    #[local] Existing Instance fully_preemptive_task_model.
    #[local] Existing Instance fully_preemptive_rtc_threshold.

    Let job_prio j := task_priority (job_task j).
    Let lower_priority task1 task2 := ~~ hep_task task1 task2.
    Let jlfp_policy j1 j2 := FP_to_JLFP hep_task j1 j2.
    Let jlfp_lower_priority j1 j2 := FP_to_JLFP lower_priority j1 j2.

    (* Let [rs] be a set of all available resources. *)
    Variable rs : seq Resource.

    (* Suppose there is a function that maps each task to a set 
       of resources that this task can use. *)
    Variable task_res : Task -> seq Resource.

    (* Consider any arrival sequence with consistent, non-duplicate arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: consistent_arrival_times arr_seq.
    Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.


    Variable sched : schedule (ideal.processor_state Job).

    Hypothesis H_jobs_come_from_arrival_sequence :
      jobs_come_from_arrival_sequence sched arr_seq.

    (* Assume we have sequential jobs. *)
    Hypothesis H_sequential_tasks : sequential_tasks arr_seq sched.

    (* (* TODO: comment *) *)
    (* Context {jr : JobReady Job PState}. *)
    (** Recall that we assume basic readiness. *)
    #[local] Instance basic_readiness : JobReady _ (ideal.processor_state Job) :=
      basic_ready_instance.


    Hypothesis H_sched_valid : valid_schedule sched arr_seq.

    Hypothesis H_work_conserving : work_conserving arr_seq sched.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute sched.


    (** Assume that a job cost cannot be larger than a task cost. *)
    Hypothesis H_valid_job_cost :
      arrivals_have_valid_job_costs arr_seq.


    (** Consider a task set [ts]. *)
    Variable ts: list Task.

    (** Let tsk be any task in [ts]. *)
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (** Next, we assume that all jobs come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* TODO: del *)
    Hypothesis H_job_pos:
      forall j, job_task j = tsk -> 0 < job_cost j.

    Context `{MaxArrivals Task}.
    Hypothesis H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals.
    Hypothesis H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts.


    (* Let's define some local names for clarity. *)
    Let task_rbf := task_request_bound_function tsk.
    Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
    Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.


    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by sched.
    Let job_backlogged_at := backlogged sched.


    (** * Definitions *)
    (* In this section we ... *)
    Section Definitions.

      (* TODO: comment *)
      Section DefinitionsRelatedToCriticalSection.

        (* We define a predicate which says if task tsk uses a resource r. *)
        Definition task_uses_resource (tsk: Task) (r: Resource) := r \in task_res tsk.

        (* TODO: check comment *)
        (* We say that job j locks a critical section r at time t, if
           job j was scheduled at time t, and service of j at time t
           is equal to lock time of the critical section r. *)
        Definition locks_at (j: Job) (cs: CriticalSection) (t: instant) :=
          (job_scheduled_at j t) && (service sched j t == cs_start cs).

        (* TODO: check comment *)
        (* We say that a critical section res remains locked by a job j at a time t if there 
           is a time moment lock_time < t in which the critical section was locked by j 
           and the critical section is still not unlocked. *)
        Definition section_remains_locked_at (j: Job) (cs: CriticalSection) (t: instant) :=
          exists lock_time,
            lock_time < t /\
            locks_at j cs lock_time /\
            cs_start cs <= service sched j t < cs_end cs.

        (* TODO: check comment *)
        (* We also introduce a computable version of section_remains_locked_at notion. *)
        Definition section_remains_locked_at_comp (j: Job) (cs: CriticalSection) (t: instant) :=
          has (fun lock_time =>
                 (locks_at j cs lock_time) && (cs_start cs <= service sched j t <  cs_end cs))
              (iota 0 t).

        (* TODO: check comment *)
        (* Next we introduce the notion of being locked for a resource. We say that the 
           resource r is locked by a job j at a time t, if there is a critical section 
           which contains resource r and (is??) locked at time t.  *)
        Definition remains_locked_at (j: Job) (r: Resource) (t: instant) :=
          exists cs: CriticalSection,
            (cs \in job_critical_sections j) /\
            (cs_resource cs = r) /\
            section_remains_locked_at j cs t.

        (* TODO: check comment *)
        (* We also introduce a computable version of remains_locked_at notion. *)
        Definition remains_locked_at_comp (j: Job) (r: Resource) (t: instant) :=
          has (fun css => section_remains_locked_at_comp j css t && (cs_resource css == r)) (job_critical_sections j).

        (* TODO: move *)
        (* TODO: comment *)
        Definition have_nonempty_intersection segment1 segment2 :=
          let '(x1, x2) := segment1 in
          let '(y1, y2) := segment2 in
          (exists t, x1 <= t < x2 /\ y1 <= t < y2).

        (* We can deduce the length of the critical section *)
        Definition cs_length (cs: CriticalSection) :=
          cs_end cs - cs_start cs.


        (* We define if two critical sections do overlap *)
        Definition cs_overlap (cs1 cs2: CriticalSection) :=
          (cs_start cs1 <= cs_start cs2 < cs_end cs1) \/ (cs_start cs2 <= cs_start cs1 < cs_end cs2).

        (* A section [cs1] is said to be a subsection of [cs2] if
           the interval of [cs1] is fully contained into the interval of [cs2].
           every section is a subsection of itself *)
        Definition cs_subsection (cs1 cs2: CriticalSection) :=
          (cs_start cs2 <= cs_start cs1) /\ (cs_end cs1 <= cs_end cs2).

        (* Two sections are nested if one of them is a subsection of the other *)
        Definition cs_nested (cs1 cs2: CriticalSection) :=
          cs_subsection cs1 cs2 \/ cs_subsection cs2 cs1.
        

        (* TODO: check comment *)
        (* First, we say that critical sections are properly formed if any section is not
           empty and has been closed before the completion of the job. *)
        Definition critical_sections_are_properly_formed :=
          forall j cs,
            (cs \in job_critical_sections j) ->
            cs_start cs < cs_end cs <= job_cost j.

        (* TODO: check comment *)
        (* Also, we can assume that the length of every critical section of some job is 
           bounded by some constant B. *)
        Definition critical_sections_are_bounded (j: Job) (B: instant) :=
          forall cs, cs \in job_critical_sections j -> cs_length cs <= B.

        (* TODO: check comment *)
        (* Further, we assume that a job cannot lock the same resource 
           twice (without previously releasing it). *)
        Definition only_one_critical_section_of_any_resource :=
          forall j cs1 cs2,
            (cs_resource cs1 = cs_resource cs2) ->
            (cs1 \in job_critical_sections j) ->
            (cs2 \in job_critical_sections j) ->
            have_nonempty_intersection (cs_start cs1, cs_end cs1) (cs_start cs2, cs_end cs2) ->
            cs1 = cs2.

        (* TODO: check comment *)
        (* Finally, we assume that critical sections are properly nested. *)
        Definition critical_sections_are_properly_nested := 
          forall j cs1 cs2,
            (cs1 \in job_critical_sections j) ->
            (cs2 \in job_critical_sections j) ->
            have_nonempty_intersection (cs_start cs1, cs_end cs1) (cs_start cs2, cs_end cs2) ->
            cs_nested cs1 cs2.

      End DefinitionsRelatedToCriticalSection.

      (* TODO: comment *)
      Section DefinitionsRelatedToPCPAlgorithm.

        (* We assign a priority to each resource, we call it priority_ceiling. The priority of a 
           resource is equal to the maximum priority of the task that uses this resource. *) 
        Definition priority_ceiling (r: Resource): nat :=
          \max_(tsk <- ts | task_uses_resource tsk r) (task_priority tsk).

        (* We define the current priority ceiling for a job j at time t, which is 
           equal to the maximum of resource priority that is locked by the job 
           j at time t. In case when there is no locked resource current 
           priority ceiling is equal to zero. *)
        Definition current_priority_ceiling (j: Job) (t: instant): nat :=
          \max_(r <- rs | (fun r => remains_locked_at_comp j r t) r) (priority_ceiling r).

        (* Finally, we can define current priority for a job j at a moment of time t. It is
           equal to the maximun between job priority and current priority ceiling of the job. *)
        Definition current_priority (j: Job) (t: instant): nat :=
          maxn (job_prio j) (current_priority_ceiling j t).

        (* Next, we describe hypotheses for the current model. 
           We say that an FP policy is respected by the schedule iff a scheduled task has 
           higher (or same) current priority than any backlogged job. *)
        Definition respects_FP_policy_with_resources :=
          forall j j_hp t,
            arrives_in arr_seq j ->
            backlogged sched j t ->
            scheduled_at sched j_hp t ->
            current_priority j_hp t >= current_priority j t.

      End DefinitionsRelatedToPCPAlgorithm.

    End Definitions.

    (** * RTA for the model *)
    (** In this section we prove ... *)
    Section Analysis.

      (* TODO: comment *)
      Section Reflect.

        (* TODO: comment *)
        Lemma section_remains_locked_atP:
          forall j cs t,
            reflect (section_remains_locked_at j cs t)
                    (section_remains_locked_at_comp j cs t).
        Proof.
          intros; apply: (iffP idP) => LOCK.
          { move: LOCK => /hasP [lt IN /andP [H5 H6]].
            exists lt; repeat split; try done.
            by move: IN; rewrite mem_iota add0n; move => /andP [_ H7].
          }
          { move: LOCK => [lt [IN [LOCK SERV]]].
            apply/hasP.
            exists lt.
            - by rewrite mem_iota add0n; apply/andP; split.
            - by apply/andP; split.
          }
        Qed.

        (* TODO: comment *)
        Lemma remains_locked_atP:
          forall j res t,
            reflect (remains_locked_at j res t) (remains_locked_at_comp j res t).
        Proof.
          intros; apply: (iffP idP) => LOCK.
          { move: LOCK => /hasP [cs IN /andP [SEC /eqP RES]].
            exists cs; repeat split; try done.
              by apply/section_remains_locked_atP.
          }
          { move: LOCK => [cs [IN [RES LOCK]]]. 
            apply/hasP.
            exists cs; try done; apply/andP; split.
            - by apply/section_remains_locked_atP.
            - by rewrite RES.
          }
        Qed.     

      End Reflect.


      Section SectionName1.


        Hypothesis H_respects_policy: respects_FP_policy_with_resources.
        
        (* TODO: move? *)
        (* TODO: *) 
        Lemma lemma17:
          forall j1 j2 t,
            arrives_in arr_seq j2 ->
            job_pending_at j1 t ->
            job_pending_at j2 t ->
            current_priority j1 t < current_priority j2 t ->
            job_backlogged_at j1 t.
        Proof.
          move => j1 j2 t ARR PEND1 PEND2 PRIO.
          have NEQ: j1 <> j2 by move => CONTR; subst j2; rewrite ltnn in PRIO.
          apply/negPn/negP; rewrite negb_and => /orP [NPEND1 | /negPn NN].
          { by exfalso; move: NPEND1 => /negPn NPEND1; apply: NPEND1. } 
          move: PRIO; rewrite ltnNge; move => /negP PRIO; apply: PRIO.
          apply H_respects_policy; try done.
          apply/andP; split; first by done.
          apply/negP; intros SCHED; apply: NEQ.
          by eapply ideal_proc_model_is_a_uniprocessor_model; eauto 1.
          (* by eapply H_uniprocessor_model; eauto. *)
        Qed.

      End SectionName1.

      (* We start with simple properties, which we will use in further proofs.  *)
      Section CeilingProperties.


        (* TODO?: up *)
        (* TODO: comment *)
        Hypothesis H_proper_sections: critical_sections_are_properly_formed.
        (* TODO: comment *)
        Hypothesis H_respects_policy: respects_FP_policy_with_resources.

        (* TODO: comment *)
        Variable j: Job.
        

        (* TODO: comment *)
        Section TodoName1.

          (* TODO: comment *)
          Variable t: instant.

          (* TODO: comment *)
          Hypothesis H_not_scheduled: ~~ job_scheduled_at j t.

          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma24:
            forall r, remains_locked_at j r t <-> remains_locked_at j r t.+1.
          Proof.
            intros r; split; intros LOCK.
            { move: LOCK => [cs [IN [RES SEC]]].
              exists cs; split; repeat split; try done.
              move: SEC => [lt [LT [LOCK /andP [SER1 SER2]]]].
              exists lt; repeat split; try done; last (apply/andP; split).
              (* - by apply ltn_trans with t. *)
              - by apply leq_trans with (service sched j t); last apply service_monotonic. 
              - apply leq_ltn_trans with (service sched j t); last by done.
                rewrite /service /service_during (@big_cat_nat _ _ _ t) //= big_nat1.
                rewrite -{2}[\sum_(0 <= t0 < t) service_at sched j t0]addn0 leq_add2l.
                by rewrite leqn0; apply/eqP; apply not_scheduled_implies_no_service.
            }
            { move: LOCK => [cs [IN [RES SEC]]].
              exists cs; repeat split; try done. 
              move: SEC => [lt [LT [LOCK /andP [SER1 SER2]]]].
              exists lt; repeat split; try done; last (apply/andP; split).
              - rewrite ltnNge; apply/negP; intros LE.
                have EQ: t = lt. by apply/eqP; rewrite eqn_leq; apply/andP; split; [ | rewrite -ltnS].
                subst lt; clear LE LT.
                move: H_not_scheduled LOCK => /negP NSCHED /andP [SCHED _].
                  by apply NSCHED.
              - apply leq_trans with (service sched j t.+1); first by done.
                rewrite /service /service_during (@big_cat_nat _ _ _ t) //= big_nat1.
                rewrite -{2}[\sum_(0 <= t0 < t) service_at sched j t0]addn0 leq_add2l.
                by rewrite leqn0; apply/eqP; apply not_scheduled_implies_no_service.
              - by apply leq_ltn_trans with (service sched j t.+1); first apply service_monotonic. 
            }
          Qed.
          
          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma20:
            current_priority_ceiling j t = current_priority_ceiling j t.+1.
          Proof.
            by apply/eqP; rewrite eqn_leq; apply/andP; split;
              apply bigmax_subset => r IN /remains_locked_atP LOCK;
              apply/remains_locked_atP; apply lemma24.
          Qed.

          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma38:
            current_priority j t = current_priority j t.+1.
          Proof.
              by rewrite /current_priority lemma20.
          Qed.

        End TodoName1.

        Section TodoName2.

          (* TODO: comment *)
          Variable t: instant.

          (* TODO: comment *)
          Variable k: nat.

          (* TODO: comment *)
          Hypothesis H_priority_ceiling_is_large_enough: k < current_priority_ceiling j t.

          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma31:
            exists r, remains_locked_at j r t.
          Proof.
            apply leq_ltn_trans with (m := 0) in H_priority_ceiling_is_large_enough => //.
            apply pos_max_implies_exists in H_priority_ceiling_is_large_enough.
            move: H_priority_ceiling_is_large_enough => [x [LOCK PRIO]].
            by exists x; apply/remains_locked_atP.
          Qed.

          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma37:
            0 < service sched j t.
          Proof.
            have NEQ2: 0 < current_priority_ceiling j t.
            { by apply leq_ltn_trans with k. }
            move: H_priority_ceiling_is_large_enough NEQ2 => _ NEQ.
            move: NEQ lemma31 => _ [r [tb1 [tb2 [_ LOCK]]]].
            move: tb1 tb2 LOCK => _ _ [lt [LT [/andP [SCHED _] _]]].
            rewrite /service /service_during (big_rem lt) //=; first last.
            { by rewrite mem_iota; apply/andP; split; last rewrite add0n subn0. }
            apply leq_trans with (service_at sched j lt); last by rewrite leq_addr.
            by apply ideal_proc_model_ensures_ideal_progress.
          Qed.

          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma41:
            job_pending_at j t.
          Proof.
            move: H_priority_ceiling_is_large_enough => CEIL.
            move: CEIL lemma31 => _ [r [cs [IN [RES [lt [LT [/andP [SCHED /eqP SERV] /andP [S1 S2]]]]]]]].
            apply/andP; split.
            - apply H_jobs_must_arrive_to_execute in SCHED.
                by apply leq_trans with lt; last apply ltnW.
            - have LE: service sched j t < job_cost j.
              { apply leq_trans with (cs_end cs); first by done.
                  by move: (H_proper_sections _ _ IN) => /andP  [_ T2].
              }
              by rewrite /completed_by -ltnNge.
          Qed.

          (* TODO: comment *)
          (* CHECK: locking? *)
          Lemma moment_of_locking_exists:
            exists rc,
              rc < t
              /\ job_scheduled_at j rc
              /\ current_priority_ceiling j rc <= k
              /\ (forall x, rc < x <= t -> k < current_priority_ceiling j x).
          Proof.
            move: H_priority_ceiling_is_large_enough => CPC; clear H_priority_ceiling_is_large_enough.
            induction t.
            - have POSt: 0 < current_priority_ceiling j 0; first by apply leq_ltn_trans with k.
              exfalso. move: POSt; rewrite lt0n; move => /negP POSt; apply: POSt.
              rewrite /current_priority_ceiling big1 //.
              move => r /remains_locked_atP [_ [_ [_ [lt [LT _]]]]].
              by rewrite ltn0 in LT.  
            - case GTLE: (k < current_priority_ceiling j i).
              { move: (IHi GTLE) => [lt [LT [SCHED [ZERO P]]]].
                exists lt; repeat split; try done.
                move => x /andP [T1 T2].
                move: T2; rewrite leq_eqVlt; move => /orP [/eqP T2|T2]; [by subst x | ].
                by apply P; apply/andP; split; last rewrite -ltnS.
              }
              { move: GTLE => /negP/negP; rewrite -leqNgt; move => LT.
                exists i; repeat split; try done.
                - apply negbNE; apply/negP; intros CONTR.
                  apply lemma20 in CONTR.
                  move: CPC; rewrite -CONTR ltnNge; move => /negP CPC.
                  by apply CPC.
                - move => x /andP [NEQ1 NEQ2].
                  have EQ: x = i.+1; first by apply/eqP; rewrite eqn_leq; apply/andP; split.
                  by subst x.
              }
          Qed.

        End TodoName2.

      End CeilingProperties.

      (** * Priority Inversion Bound *)
      (** The main contribution of this section will be the proof of the fact that
         the length of a priority inversion should be bounded with some constant. 
         After this, it is possible to use the General RTA(?) theorem to get a 
         proof of (?) correctness for this model. *)
      Section PriorityInversionIsBounded.


        (* TODO?: up *)
        (* TODO: comment *)
        Hypothesis H_proper_sections: critical_sections_are_properly_formed.
        (* TODO: comment *)
        Hypothesis H_respects_policy: respects_FP_policy_with_resources.


        (** Non-overlapping priorities property. *)
        (** In this section we prove a property that says that the
            base priority and the ceiling priority of one job don't
            overlap with priorities of another job. More formaly,
            suppose there are two jobs [j1] and [j2]. Let the jobs
            hold some resource at time [t], so both of them have
            raised priority (due to ceiling). Then we prove that
            either the base priority of job [j1] is not smaller that
            ceiled priotiry of job [j2], or vice versa. *)
        Section NonOverlappingPriorities.

          (* Let us show a detailed proof of this fact. We begin with an asymmetrical 
             version of the lemma in which we assume the job j1 starts executing earlier 
             than j2. Further using case analysis we will get a lemma which does not 
             depend on that assumption. *)
          Section NonOverlapAsymmetricalLemma.
 
            (* TODO: comment *)
            Variables j1 j2: Job.
            Hypothesis H_not_equal: j1 <> j2.

            (* Consider any time t. *)
            Variable t: instant.

            (* TODO: comment *)
            (* TODO: name *)
            Hypothesis H_ceiling_of_j1_is_active: job_prio j1 < current_priority_ceiling j1 t.
            Hypothesis H_ceiling_of_j2_is_active: job_prio j2 < current_priority_ceiling j2 t.

            (* TODO: names *)
            (* TODO: comment *)
            (* We can prove that there exists ... *)
            Variables t_j1: instant.
            Hypothesis EX1: job_scheduled_at j1 t_j1 /\ service sched j1 t_j1 = 0.

            (* TODO: comment *)
            Variable t_j2: instant.
            Hypothesis EX2: job_scheduled_at j2 t_j2 /\ service sched j2 t_j2 = 0.

            (* TODO: comment *)
            Hypothesis LTj1j2: t_j1 < t_j2.

            (* TODO: comment *)
            Variable rc1: instant.
            Hypothesis N1 : rc1 < t.
            Hypothesis SCHEDrc1 : job_scheduled_at j1 rc1.
            Hypothesis PRIOrc1 : current_priority_ceiling j1 rc1 <= job_prio j1.
            Hypothesis PRIO2c1 : forall x : instant, rc1 < x <= t -> job_prio j1 < current_priority_ceiling j1 x.

            (* TODO: comment *)
            Variable rc2: instant. 
            Hypothesis N2: rc2 < t.
            Hypothesis SCHEDrc2: job_scheduled_at j2 rc2.
            Hypothesis PRIOrc2: current_priority_ceiling j2 rc2 <= job_prio j2.
            Hypothesis PRIO2c2: forall x: instant, rc2 < x <= t -> job_prio j2 < current_priority_ceiling j2 x.


            (* TODO: comment *)
            (* TODO: name *)
            (* Simple fact *)
            Lemma PEND1:
              forall x,
                t_j1 <= x <= t ->
                job_pending_at j1 x.
            Proof.
              move => t0 /andP [NEQ1 NEQ2].
              move: EX1 => [SCHEDj1a SERVj1a].
              eapply scheduled_implies_pending in SCHEDj1a; eauto 2.
              apply lemma41 in H_ceiling_of_j1_is_active; auto.
              move: SCHEDj1a H_ceiling_of_j1_is_active => /andP [ARR _] /andP [_ NCOMP].
              apply/andP; split.
              - by apply leq_trans with t_j1.
              - apply/negP; intros NCOM; move: NCOMP => /negP T; apply: T.
                  by eapply completion_monotonic with t0.
            Qed.

            (* TODO: comment *)
            (* Simple fact *)
            (* TODO: name *)
            Lemma PEND2:
              forall x,
                t_j2 <= x <= t ->
                job_pending_at j2 x.
            Proof.
              move => t0 /andP [NEQ1 NEQ2].
              move: EX2 => [SCHEDj2a SERVj2a].
              eapply scheduled_implies_pending in SCHEDj2a; eauto 2.
              apply lemma41 in H_ceiling_of_j2_is_active; auto.
              move: SCHEDj2a H_ceiling_of_j2_is_active => /andP [ARR _] /andP [_ NCOMP].
              apply/andP; split.
              - by apply leq_trans with t_j2.
              - apply/negP; intros NCOM; move: NCOMP => /negP T; apply: T.
                  by eapply completion_monotonic with t0.
            Qed.
              

            (* TODO: name *)
            (* TODO: comment *)
            (* Simple fact *)
            Lemma NE1: t_j1 <= rc1.
            Proof.
              move: EX1 EX2 => [SCHEDj1a SERVj1a] [SCHEDj2a SERVj2a].
              rewrite leqNgt; apply/negP; intros CONTR.
              move: SERVj1a => /eqP; rewrite -leqn0 leqNgt; move => /negP T; apply: T.
              rewrite /service /service_during (big_rem rc1) //=; last first.
              { by rewrite mem_iota; apply/andP; split; last rewrite add0n subn0. }
              apply leq_trans with (service_at sched j1 rc1); last by rewrite leq_addr.
              by apply ideal_proc_model_ensures_ideal_progress.
            Qed.
            
            (* TODO: comment *)
            (* Simple fact *)
            Lemma NE2: t_j2 <= rc2.
            Proof.
              move: EX1 EX2 => [SCHEDj1a SERVj1a] [SCHEDj2a SERVj2a].
              rewrite leqNgt; apply/negP; intros CONTR.
              move: SERVj2a => /eqP; rewrite -leqn0 leqNgt; move => /negP T; apply: T.
              rewrite /service /service_during (big_rem rc2) //=; last first.
              { by rewrite mem_iota; apply/andP; split; last rewrite add0n subn0. }
              apply leq_trans with (service_at sched j2 rc2); last by rewrite leq_addr.
              by apply ideal_proc_model_ensures_ideal_progress.
            Qed.
            
            (* TODO: comment *)
            (* Simple fact *)
            Lemma NE3: t_j1 <= rc2.
            Proof.
              have NE1 := NE1.
              have NE2 := NE2.
                by apply leq_trans with t_j2; first apply ltnW.
            Qed.

            
            (* TODO: fix comment *)
            (* TODO: name *)
            (* Since j2 is scheduled at time rc2
               and rc2 is the first time ... => job_prio j2 is no less than current_priority j1 at time rc2. *)
            Lemma F1:
              current_priority j1 rc2 <= job_prio j2.
            Proof.
              have NE1 := NE1.
              have NE2 := NE2.
              have NE3 := NE3.
              have OOJS: forall t, job_scheduled_at j1 t -> job_scheduled_at j2 t -> False.
              { by intros x SC1 SC2; eapply H_not_equal, ideal_proc_model_is_a_uniprocessor_model; eauto 2. }
              have FBACK: forall t, job_pending_at j1 t -> job_scheduled_at j2 t -> job_backlogged_at j1 t.
              { intros x PEND SCHED.
                apply/andP; split; first by done.
                apply/negP; intros SCHED2.
                  by move: (OOJS _ SCHED2 SCHED).
              }
              apply leq_trans with (current_priority j2 rc2).
              - apply H_respects_policy; try done.
                (* + by eapply H_jobs_come_from_arrival_sequence; eauto 2. *)
                + apply FBACK; try done.
                  by apply PEND1; apply/andP; split; last apply ltnW.
              - by rewrite geq_max; apply/andP; split.
            Qed.

            
            (* TODO: fix comment *)
            (* TODO: name *)
            (* *)
            Lemma F2:
              forall x,
                rc2 <= x <= t ->
                current_priority j1 x <= job_prio j2.
            Proof.
              have OOJS: forall t, job_scheduled_at j1 t -> job_scheduled_at j2 t -> False.
              { by intros x SC1 SC2; eapply H_not_equal, ideal_proc_model_is_a_uniprocessor_model; eauto 2. }
              have FBACK: forall t, job_pending_at j1 t -> job_scheduled_at j2 t -> job_backlogged_at j1 t.
              { intros x PEND SCHED.
                apply/andP; split; first by done.
                apply/negP; intros SCHED2.
                  by move: (OOJS _ SCHED2 SCHED).
              }

              have NE1 := NE1.
              have NE2 := NE2.
              have NE3 := NE3.
              have ARR1: arrives_in arr_seq j1; first by eapply H_jobs_come_from_arrival_sequence; eauto 2.
              have ARR2: arrives_in arr_seq j2; first by eapply H_jobs_come_from_arrival_sequence; eauto 2.
              
              intros x TT.
              have EX: exists k, x = rc2 + k.
              { by exists (x - rc2); rewrite subnKC; last move: TT => /andP [TT _]. } move: EX => [k EQ].
              subst x.
              induction k.
              - by rewrite addn0; apply F1.
              - feed IHk.
                { apply/andP; split.
                  - by rewrite leq_addr.
                  - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: TT => /andP [_ TT]].
                }
                have BACK: job_backlogged_at j1 (rc2 + k).
                { move: (posnP k) => [ZE | POS].
                  { subst k; rewrite addn0. apply FBACK; last by done.
                      by apply PEND1; apply/andP; split; last apply ltnW.
                  }
                  have PRIO: current_priority j1 (rc2 + k) < current_priority j2 (rc2 + k).
                  { apply leq_ltn_trans with (job_prio j2); first by done.
                    rewrite leq_max; apply/orP; right.
                    apply PRIO2c2.
                    apply/andP; split.
                    - by rewrite -addn1 leq_add2l.
                    - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: TT => /andP [_ TT]].
                  }
                  apply lemma17 with j2; try done.
                  apply PEND1; try done.
                  { apply/andP; split.
                    - by apply leq_trans with rc2; last rewrite leq_addr.
                    - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: TT => /andP [T1 T2]].
                  }
                  apply PEND2; try done.
                  { apply/andP; split.
                    - by apply leq_trans with rc2; last by rewrite leq_addr.
                    - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: TT => /andP [T1 T2]].
                  }
                }
                move: BACK => /andP [_ NSCHED].
                  by rewrite addnS -lemma38.
            Qed.

            (* TODO: comment *)
            Lemma F3:
              forall x,
                rc2 < x <= t ->
                current_priority j1 x < current_priority j2 x.
            Proof.
              move => x /andP [NEQ1 NEQ2].
              apply leq_ltn_trans with (job_prio j2).
              - by apply F2; apply/andP; split; first apply ltnW.
              - rewrite leq_max; apply/orP; right. 
                by apply PRIO2c2; apply/andP; split.
            Qed.


            (* TODO: comment *)
            Lemma F4:
              forall x,
                rc2 <= x <= t ->
                job_backlogged_at j1 x.
            Proof.
              have OOJS: forall t, job_scheduled_at j1 t -> job_scheduled_at j2 t -> False.
              { by intros x SC1 SC2; eapply H_not_equal, ideal_proc_model_is_a_uniprocessor_model; eauto 2. }
              have FBACK: forall t, job_pending_at j1 t -> job_scheduled_at j2 t -> job_backlogged_at j1 t.
              { intros x PEND SCHED.
                apply/andP; split; first by done.
                apply/negP; intros SCHED2.
                  by move: (OOJS _ SCHED2 SCHED).
              }
              have NE1 := NE1.
              have NE2 := NE2.
              have NE3 := NE3.
              have ARR1: arrives_in arr_seq j1; first by eapply H_jobs_come_from_arrival_sequence; eauto 2.
              have ARR2: arrives_in arr_seq j2; first by eapply H_jobs_come_from_arrival_sequence; eauto 2.              
              move => x /andP [NEQ1 NEQ2].
              move: NEQ1; rewrite leq_eqVlt; move => /orP [/eqP EQ | LT].
              { subst x.
                apply FBACK; last by done.
                apply PEND1; apply/andP; split; last by done.
                  by apply ltnW, leq_trans with t_j2.
              }
              { apply lemma17 with j2; try done.
                - apply PEND1; apply/andP; split; last by done.
                  apply leq_trans with rc2.
                    by apply ltnW, leq_trans with t_j2. by apply ltnW.
                - apply PEND2; apply/andP; split; last by done.
                    by apply leq_trans with rc2; last apply ltnW.
                - by apply F3; apply /andP; split.
              }
            Qed.


            (* TODO: comment *)
            (* TODO: name *)
            Lemma lemma36:
              forall j t1 t2,
                t1 <= t2 ->
                (forall t, t1 <= t < t2 -> job_backlogged_at j t) ->
                current_priority j t1 = current_priority j t2.
            Proof.
              intros j t1 t2 NEQ ALL.
              have EX: exists k, t2 = t1 + k.
              { by exists (t2 - t1); rewrite subnKC. }
              move: EX => [k EQ].
              subst t2. clear NEQ. 
              induction k.
              - by rewrite addn0. 
              - feed IHk.
                { intros l NEQ; apply ALL.
                  move: NEQ => /andP [T1 T2].
                  apply/andP; split; first by done.
                    by apply ltn_trans with (t1 + k); last rewrite addnS.
                } 
                rewrite IHk.
                rewrite addnS; apply lemma38.
                { specialize (ALL (t1+k)); feed ALL.
                  { by apply/andP; split; [rewrite leq_addr | rewrite addnS]. }
                  by move: ALL => /andP [_ NSCHED].
                }
            Qed.

            (* TODO: comment *)
            Lemma F5:
              current_priority j1 rc2 = current_priority j1 t.
            Proof.
              apply lemma36; first by apply ltnW.
              move => x /andP [T1 T2]; apply ltnW in T2.
                by apply F4; apply/andP; split.
            Qed.
            
            (* TODO: comment *)
            Lemma ceiling_property_help:
              current_priority_ceiling j1 t <= job_prio j2.
            Proof.
              have OOJS: forall t, job_scheduled_at j1 t -> job_scheduled_at j2 t -> False.
              { by intros x SC1 SC2; eapply H_not_equal, ideal_proc_model_is_a_uniprocessor_model; eauto 2. }
              
              move: EX1 EX2 => [SCHEDj1a SERVj1a] [SCHEDj2a SERVj2a].
              move: (ltngtP t_j2 rc1) => [PR2|PR2|CONTR].
              { move: (ltngtP rc1 rc2) => [PR3|PR3|CONTR].
                { apply leq_trans with (current_priority j1 rc2); last by apply F1.
                  rewrite F5.
                    by rewrite leq_maxr.
                }
                { apply leq_trans with (current_priority j1 rc2); last by apply F1.
                  rewrite F5.
                    by rewrite leq_maxr.
                }
                { by exfalso; subst rc2; move: (OOJS _ SCHEDrc1 SCHEDrc2). }
              }
              { apply leq_trans with (current_priority j1 rc2); last by apply F1.
                rewrite F5.
                  by rewrite leq_maxr.
              }
              { by exfalso; subst t_j2; move: (OOJS _ SCHEDrc1 SCHEDj2a). }
            Qed.

          End NonOverlapAsymmetricalLemma.

          (* TODO: explanation *)
          Section NonOverlapLemma.
            
            (* TODO: comment *)
            Variables j1 j2: Job.
            Hypothesis H_not_equal: j1 <> j2.

            (* Consider any time t. *)
            Variable t: instant.

            (* TODO: comment *)
            Hypothesis CPC1: job_prio j1 < current_priority_ceiling j1 t.
            Hypothesis CPC2: job_prio j2 < current_priority_ceiling j2 t.
            
            (* TODO: comment *)
            Lemma ceiling_property:
              current_priority_ceiling j1 t <= job_prio j2
              \/ current_priority_ceiling j2 t <= job_prio j1.
            Proof.
              have UT1: forall t, job_scheduled_at j1 t -> job_scheduled_at j2 t -> False.
              { by intros x SC1 SC2; eapply H_not_equal, ideal_proc_model_is_a_uniprocessor_model; eauto 2. }
              have EX1: exists j1a, job_scheduled_at j1 j1a /\ service sched j1 j1a = 0.
              { apply lemma37 in CPC1.
                apply incremental_service_during in CPC1 => //.
                (* apply exists_intermediate_service_ext in CPC1 => //. *)
                move: CPC1 => [j1a [_ [SCHED SERV]]].
                exists j1a; repeat split; try done.
              }
              have EX2: exists j2a, job_scheduled_at j2 j2a /\ service sched j2 j2a = 0.
              { apply lemma37 in CPC2.
                apply incremental_service_during in CPC2 => //.
                move: CPC2 => [j2a [_ [SCHED SERV]]].
                exists j2a; repeat split; try done.
              }
              move: EX1 EX2 => [j1a [SCHEDj1a SERVj1a]] [j2a [SCHEDj2a SERVj2a]].
              move: (moment_of_locking_exists j1 t _ CPC1) (moment_of_locking_exists j2 t _ CPC2) =>
                    [rc1 [N1 [SCHEDrc1 [PRIOrc1 PRIO2c1]]]] [rc2 [N2 [SCHEDrc2 [PRIOrc2 PRIO2c2]]]].
              move: (H_not_equal) => /neqP; rewrite eq_sym; move => /neqP NEQsym.
              move: (ltngtP j1a j2a) => [PR1|PR1|CONTR].
              - by left; eapply ceiling_property_help with (rc1 := rc1); eauto 2.
              - by right; eapply ceiling_property_help with (rc2 := rc1); eauto 2.
              - by exfalso; subst j2a; move: (UT1 _ SCHEDj1a SCHEDj2a).
            Qed.

          End NonOverlapLemma.

        End NonOverlappingPriorities.

        
        Lemma lemma42:
          forall jlp j,
            jlfp_lower_priority jlp j ->
            job_prio jlp < job_prio j.
        Proof.
          intros jlp jhp.
          by rewrite /jlfp_lower_priority/lower_priority /FP_to_JLFP /hep_task /NumericFPAscending -ltnNge.
        Qed.          

        Lemma lemma43:
          forall jhp jlp,
            jlfp_policy jhp jlp ->
            job_prio jlp <= job_prio jhp.        
        Proof.
          by intros jhp jlp.
        Qed.

        
        (** Only _one_ lower priority job can cause blocking. *)
        (* In this section we prove that for any job j there might be at most one
           lower priority job jlp which causes delay due to blocking. *)
        Section OnlyOneLowerPriorityJobCanCauseBlocking.

          (* Consider any job j of tsk. *)
          Variable j: Job.
          Hypothesis H_j_arrives: arrives_in arr_seq j.
          Hypothesis H_job_of_tsk: job_task j = tsk.

          (* TODO: comment *)
          (* Consider any busy interval [t1, t2)... *)
          Variable t1 t2: instant.
          Hypothesis H_busy_interval_prefix:
            busy_interval_prefix arr_seq sched j t1 t2.

          (* In this section we prove that a job with a lower priority should raise 
             priority (= lock some resource) in order to execute inside busy interval. *)
          Section LowerPriorityJobShouldRaisePriority.

            (* TODO: comment *)
            Variable t: instant.
            Hypothesis H_t_inside_busy_interval: t1 <= t < t2.

            (* Consider any job jlp with lower priority. *)
            Variable jlp: Job.
            Hypothesis H_lower_priority: jlfp_lower_priority jlp j. 

    
            (* TODO: comment *)
            Lemma lp_job_can_be_scheduled_inside_busy_interval_only_with_locked_resource:
              job_scheduled_at jlp t ->
              current_priority_ceiling jlp t > 0.
            Proof.
              intros SCHED.
              move: H_lower_priority => LP.
              move: (H_busy_interval_prefix) => PREF.
              move: H_t_inside_busy_interval => /andP [GE LT].
              have EX:
                exists jhp,
                  jhp <> jlp /\
                  arrives_in arr_seq jhp /\
                  job_backlogged_at jhp t /\
                  jlfp_policy jhp j.
              { intros.
                have P := pending_hp_job_exists
                            arr_seq _ sched _ j _ _ _ _ _ PREF t.
                feed_n 6 P => //.
                (* { by move => s; rewrite /hep_job / jlfp_policy /FP_to_JLFP /hep_task /NumericFPAscending. } *)
                move: P => [jhp [ARR [PEN HP]]].
                exists jhp; repeat split; try done.
                { by intros EQ; subst jlp; move: LP => /negP LP; apply: LP. } 
                { apply/andP; split; first by done.
                  apply/negP; intros CONTR.
                  have OK:= ideal_proc_model_is_a_uniprocessor_model _ _ _ _ SCHED CONTR; subst jlp.
                  by move: LP => /negP LP; apply: LP.
                }
              }
              move: EX => [jhp [NEQj [ARRjhp [BACK HP]]]].
              move: (H_respects_policy jhp jlp t ARRjhp BACK SCHED) => PRIO.
              have ALT: forall n, n = 0 \/ n > 0.
              { by clear; intros n; destruct n; [left | right ]. }
              move: (ALT (current_priority_ceiling jlp t)) => [ZERO | POS].
              { exfalso.
                move: PRIO; rewrite /current_priority ZERO maxn0 geq_max; move => /andP [PRIO _].
                move: PRIO. rewrite leqNgt; move => /negP PRIO; apply: PRIO.
                apply leq_trans with (job_prio j).
                by apply lemma42.
                by apply lemma43.
              }
              by done.
            Qed.
            
            (* TODO: comment *)
            Lemma lp_job_cannot_be_scheduled_inside_busy_interval:
              current_priority jlp t1 < job_prio j ->
              ~~ job_scheduled_at jlp t.
            Proof.
              intros PRIO.
              move: (H_busy_interval_prefix) => PREF.
              have helper:
                forall t,
                  t1 <= t < t2 ->
                  current_priority jlp t < job_prio j ->
                  ~~ job_scheduled_at jlp t.
              { clear H_t_inside_busy_interval PRIO t; intros t NEQ PRIO.
                case PEND: (job_pending_at jlp t).
                have EX := pending_hp_job_exists
                             arr_seq _ sched _ j _ _ _ _ _ PREF t.
                feed_n 6 EX => //.
                (* { by move => s; rewrite /hep_job / jlfp_policy /FP_to_JLFP /hep_task /NumericFPAscending. } *)
                move: EX => [jhp [ARR [PEN HP]]].
                move: (lemma17 H_respects_policy _ _ _ ARR PEND PEN) => BACK.
                feed BACK.
                { apply leq_trans with (job_prio j); first by done.
                  rewrite /current_priority leq_max; apply/orP; left.
                  by apply lemma43.
                }
                by move: BACK => /andP [_ NSCHED].
                - move: PEND; rewrite /job_pending_at /pending; move => /negP /negP PEND.
                  move: PEND; rewrite negb_and; move => /orP [NARR | COMPL].
                  { apply/negP; intros SCHED.
                    apply H_jobs_must_arrive_to_execute in SCHED.
                    by move: NARR => /negP NARR; apply: NARR.
                  }
                  { by apply negbNE, completed_implies_not_scheduled in COMPL. }
              }
              apply helper; try done.
              have EX: exists k, t = t1 + k.
              { by exists (t - t1); rewrite subnKC; last move: H_t_inside_busy_interval => /andP [T _]. }
              move: EX => [k EQ]; subst t.
              induction k.
              - by rewrite addn0.
              - have NEQ2: t1 <= t1 + k < t2.
                { move: H_t_inside_busy_interval => /andP [T1 T2].
                  apply/andP; split; first by rewrite leq_addr.
                  by apply ltn_trans with (t1 + k.+1); first rewrite addnS.
                } feed IHk; first by done.
                move: (helper _ NEQ2 IHk) => NSCHED.
                apply lemma38 in NSCHED.
                by rewrite addnS -NSCHED.
            Qed.
            
            (* TODO: comment *)
            Lemma lp_job_can_be_scheduled_inside_busy_interval_only_with_raised_priority:
              job_scheduled_at jlp t ->
              job_prio j <= current_priority_ceiling jlp t1.
            Proof.
              intros SCHED.
              rewrite leqNgt; apply/negP; intros PRIO.
              move: SCHED ; rewrite -[job_scheduled_at _ _]Bool.negb_involutive => /negP SCHED; apply: SCHED.
              apply lp_job_cannot_be_scheduled_inside_busy_interval.
              rewrite gtn_max; apply/andP; split; last by done.
              by apply lemma42.
            Qed.

          End LowerPriorityJobShouldRaisePriority.
          
          (* TODO: comment *)
          Lemma only_one_lower_priority_job_can_block:
            forall jlp1 jlp2 t' t'',
              t1 <= t' < t2 ->
              t1 <= t'' < t2 ->
              jlfp_lower_priority jlp1 j ->
              jlfp_lower_priority jlp2 j ->
              job_scheduled_at jlp1 t' ->
              job_scheduled_at jlp2 t'' ->
              jlp1 = jlp2.
          Proof.
            intros jlp1 jlp2 t' t'' NEQ1 NEQ2 LP1 LP2 SCHED1 SCHED2.
            apply/eqP/neqP; intros NEQ.
            move: (lp_job_can_be_scheduled_inside_busy_interval_only_with_locked_resource _ NEQ1 _ LP1 SCHED1) => INCS1.
            move: (lp_job_can_be_scheduled_inside_busy_interval_only_with_locked_resource _ NEQ2 _ LP2 SCHED2) => INCS2.
            have INCS3: job_prio jlp1 < current_priority_ceiling jlp1 t1.
            { rewrite ltnNge; apply/negP; intros CONTR.
              have PRIO: current_priority jlp1 t1 <= job_prio jlp1.
              { by rewrite geq_max; apply/andP; split. }
              have PRIO2: current_priority jlp1 t1 < job_prio j.
              { apply leq_ltn_trans with (job_prio jlp1); first by done.
                by apply lemma42.
              }
              apply lp_job_cannot_be_scheduled_inside_busy_interval with (t := t') in PRIO2; try done.
                by move: PRIO2 => /negP PRIO2; apply: PRIO2.
            }
            have INCS4: job_prio jlp2 < current_priority_ceiling jlp2 t1.
            { rewrite ltnNge; apply/negP; intros CONTR.
              have PRIO: current_priority jlp2 t1 <= job_prio jlp2.
              { by rewrite geq_max; apply/andP; split. }
              have PRIO2: current_priority jlp2 t1 < job_prio j.
              { apply leq_ltn_trans with (job_prio jlp2); first by done.
                by apply lemma42.
              }
              apply lp_job_cannot_be_scheduled_inside_busy_interval with (t := t'') in PRIO2; try done.
                by move: PRIO2 => /negP PRIO2; apply: PRIO2.
            }
            move: INCS1 INCS2 INCS3 INCS4 => _ _ INCS1 INCS2.
            move: (lp_job_can_be_scheduled_inside_busy_interval_only_with_raised_priority _ NEQ1 _ LP1 SCHED1) => PRIO1.
            move: (lp_job_can_be_scheduled_inside_busy_interval_only_with_raised_priority _ NEQ2 _ LP2 SCHED2) => PRIO2.
            move: (ceiling_property jlp1 jlp2 NEQ t1) => KEK.
            feed_n 2 KEK; try done.
            move: KEK => [T|T]; exfalso.
            - exfalso.
              apply leq_trans with (m := job_prio j) in T; last by done.
              apply lemma42 in LP2.
              lia.
            - exfalso.
              apply leq_trans with (m := job_prio j) in T; last by done.
              apply lemma42 in LP1.
              lia.
          Qed.
          
        End OnlyOneLowerPriorityJobCanCauseBlocking.

        (** Blocking length is bounded. *)
        (* TODO: comment *)
        Section BlockingLength.

          (* TODO: comment *)
          Variable j: Job.

          (* TODO: comment *)
          Variable B: instant.
          Hypothesis H_B_positive: B > 0.
          
          (* TODO: comment *)
          Hypothesis H_critical_sections_are_bounded: critical_sections_are_bounded j B.

          (* TODO: comment *)
          Hypothesis H_resource_locks_are_properly_nested: critical_sections_are_properly_nested.

          (* TODO: comment *)
          Hypothesis H_only_one_section_of_any_resource: only_one_critical_section_of_any_resource. 

          (* TODO: comment  *)
          Lemma earlier_resource_locks_earlier:
            forall cs1 cs2 t1 t2,
              cs_start cs1 <= cs_start cs2 ->
              locks_at j cs1 t1 ->
              locks_at j cs2 t2 ->
              t1 <= t2.
          Proof.
            intros ? ? ? ? NEQ LOCK1 LOCK2.
            move: LOCK1 LOCK2 => /andP [SCHED1 /eqP SERV1] /andP [SCHED2 /eqP SERV2].
            rewrite leqNgt; apply/negP; intros NEQ1.
            move: (NEQ1) => NEQ2; apply ltnW in NEQ2.
            move: NEQ; rewrite leqNgt; move => /negP NEQ; apply: NEQ.
            rewrite -SERV1 -SERV2.
            rewrite [X in _ < X](@big_cat_nat _ _ _ t2) //=.
            rewrite -addn1 leq_add2l.
            rewrite (big_rem t2) //=.
            - apply leq_trans with (service_at sched j t2); last by rewrite leq_addr.
              by apply ideal_proc_model_ensures_ideal_progress.
            - by rewrite mem_iota subnKC //; apply/andP; split.
          Qed.

          (* TODO: comment *)
          Section ResourceCannotBeLockedTwiceInRow.

            (* TODO: comment *)
            Lemma cannot_be_locked_twice_in_row_induction_base:
              forall t cs1 cs2,
                (cs_resource cs1 = cs_resource cs2) ->
                (cs1 \in job_critical_sections j) ->
                section_remains_locked_at j cs1 t ->

                (cs2 \in job_critical_sections j) ->
                section_remains_locked_at j cs2 t ->

                cs1 = cs2.
            Proof.
              intros ? ? ? EQ IN1 LOCK1 IN2 LOCK2.
              move: LOCK1 LOCK2 =>[lt1 [LT1 [/andP [SCHED1 /eqP ES1] SERV1]]][lt2 [LT2 [/andP [SCHED2 /eqP ES2] SERV2]]].
              simpl in *.
              apply H_only_one_section_of_any_resource with j; try done.
                by exists (service sched j t); split.
            Qed.

            (* TODO: comment *)
            Lemma cannot_be_locked_twice_in_row_induction_step:
              forall t cs1 cs2,
                (cs_resource cs1 = cs_resource cs2) ->
                (cs1 \in job_critical_sections j) ->
                section_remains_locked_at j cs1 t ->

                (cs2 \in job_critical_sections j) ->
                section_remains_locked_at j cs2 t.+1 ->

                cs1 = cs2.
            Proof.
              intros ? ? ? EQ IN1 LOCK1 IN2 LOCK2.
              move: LOCK1 LOCK2 => [lt1 [LT1 [/andP [SCHED1 /eqP ES1] SERV1]]][lt2 [LT2 [/andP [SCHED2 /eqP ES2] SERV2]]].
              simpl in *.
              apply H_only_one_section_of_any_resource with j; try done.
              exists (service sched j t); split; first by done.
              apply/andP; split; last first.
              - apply leq_ltn_trans with (service sched j (t.+1)); last by move: SERV2 => /andP [T1 T2].
                  by rewrite /service /service_during big_nat_recr //= leq_addr.
              - have L1: service sched j lt2 < service sched j t.+1.
                { rewrite -(service_cat _ _ lt2 t.+1); last by lia.
                  rewrite -service_during_first_plus_later //.
                  rewrite -addn1 leq_add2l.
                  rewrite -addn1 addnC leq_add //.
                  by apply ideal_proc_model_ensures_ideal_progress.
                }
                have SERV3: cs_start cs2 < service sched j t.+1 < cs_end cs2.
                { by apply/andP; split; [rewrite -ES2 | move: SERV2 => /andP [T1 T2]]. }
                move: SERV2 SERV3 => _ SERV2.
                have POS: 0 < service sched j t.+1.
                { by apply leq_ltn_trans with (cs_start cs2); last move: SERV2 => /andP [T1 T2]. }
                apply leq_trans with (service sched j (t.+1) - 1).
                { by rewrite -ES2 -(leq_add2r 1) subn1 !addn1 prednK //. }
                rewrite -(leq_add2r 1) subn1 addn1 prednK //.
                rewrite /service /service_during (@big_cat_nat _ _ _ (t)) //=.
                rewrite leq_add2l.
                rewrite big_nat1.
                by apply service_at_most_one.
            Qed.

            (* TODO: comment *)
            Lemma cannot_be_locked_twice_in_row:
              forall t1 t2 cs1 cs2,
                t1 <= t2 ->
                ( cs_resource cs1 = cs_resource cs2 ) -> 
                (forall t, t1 <= t < t2 -> remains_locked_at j (cs_resource cs1) t ) ->

                (cs1 \in job_critical_sections j) ->
                section_remains_locked_at j cs1 t1 -> 
                
                (cs2 \in job_critical_sections j) ->
                section_remains_locked_at j cs2 t2 ->
                
                cs1 = cs2.
            Proof.
              intros ? ? ? ? LE EQr ICS IN1 LOCK1 IN2 LOCK2.
              have EX: exists k, t2 = t1 + k.
              { by exists (t2 - t1); rewrite subnKC. }
              move: EX => [k EQ]; subst t2; clear LE.
              induction k.
              { by rewrite addn0 in LOCK2; apply cannot_be_locked_twice_in_row_induction_base with (t := t1). }
              { apply: IHk.
                { intros; apply ICS.
                  move: H5 => /andP [T1 T2].
                  apply/andP; split; first by done.
                  apply ltn_trans with (t1 + k); first by done.
                    by rewrite addnS. }
                { feed (ICS (t1+k)).
                  { by apply/andP; split; [rewrite leq_addr | rewrite addnS]. }
                  move: ICS => [cs [IN [RES LOCK]]].
                  rewrite addnS in LOCK2.
                  rewrite -(cannot_be_locked_twice_in_row_induction_step (t1+k) cs cs2); try done.
                    by rewrite RES.
                }
              }
            Qed.
            
          End ResourceCannotBeLockedTwiceInRow.

          (* We prove that if there is a time interval and at each moment in this interval
             there is a resource that is locked at that time, then there is one outer 
             resource that remains locked throughout the entire time interval *)
          Lemma existence_of_outer_resource:
            forall t1 t2,
              t1 <= t2 ->
              (     forall t, t1 <= t <= t2 -> exists r, remains_locked_at j r t) ->
              (exists r, forall t, t1 <= t <= t2 ->      remains_locked_at j r t).
          Proof.
            intros ? ? LE T.
            have EX: exists k, t2 = t1 + k.
            { by exists (t2 - t1); rewrite subnKC. }
            move: EX => [k EQ]; subst t2; clear LE.
            induction k.
            - feed (T t1); first by rewrite addn0; apply/andP; split.
              move: T => [r HLB].
              exists r; intros.
                by move: H5; rewrite addn0 -eqn_leq; move => /eqP H5; subst t.
            - feed IHk.
              { move => t /andP [T1 T2].
                apply T; apply/andP; split; first by done.
                apply leq_trans with (t1 + k); first by done.
                  by rewrite addnS.
              }
              feed (T (t1 + k.+1)).
              { by apply/andP; split; first rewrite leq_addr //. }
              move: T => [rl LOCKrl].
              move: IHk => [ro LOCKro].
              case LOCKo: (remains_locked_at_comp j ro (t1+k.+1)).
              { exists ro.
                move => t /andP [N1 N2].
                move: N2; rewrite leq_eqVlt; move => /orP [/eqP N2| N2].
                { by subst t; apply/remains_locked_atP. }
                  by apply LOCKro; apply/andP; split; rewrite addnS ltnS in N2.
              }
              {

                move: LOCKrl => [cs1 [INl [RESl [ltl [LTl [Hl H2l]]]]]].
                move: (LOCKro (t1 + k)) => L.
                feed L.
                { by apply/andP; split; first rewrite leq_addr. }

                move: L => [cs2 [INo [RESo To]]].
                move: (To) => [lto [LTo [Ho H2o]]].
                
                have NEQ1: (cs_end cs1) > (cs_end cs2).
                { rewrite ltnNge; apply/negP; intros NEQ.
                  move: LOCKo => /negP LOCKo; apply: LOCKo.
                  apply/remains_locked_atP.
                  unfold remains_locked_at.
                  exists cs2; repeat split; try done.
                  exists lto.
                  split. apply ltn_trans with (t1 + k).  by done.  by rewrite addnS.
                  split. by done.
                  apply/andP; split.
                  move: (H2o) => /andP [H2o1 H2o2].
                  apply leq_trans with (service sched j (t1 + k)); first by done.
                  apply service_monotonic; rewrite addnS; by done.
                  apply leq_trans with (cs_end cs1); last by done.
                    by move: H2l => /andP [T1 T2].
                }
                
                have NEQ2: (cs_start cs1) <= (cs_start cs2).
                { specialize (H_resource_locks_are_properly_nested j _ _ INl INo).
                  feed H_resource_locks_are_properly_nested.
                  { exists (service sched j (t1 + k)); split; last by done.
                    apply/andP; split; last first.
                    { apply leq_ltn_trans with (service sched j (t1+ k.+1)); last by move: H2l => /andP [T1 T2].
                        by rewrite /service /service_during addnS big_nat_recr //= leq_addr.
                    }
                    { have L1: (cs_start cs1) < service sched j (t1 + k.+1).
                      { move: Hl => /andP [SCHED /eqP ES]; simpl in ES.
                        rewrite -ES.
                        rewrite -[in X in _ < X](service_cat _ _ ltl _); last by lia.
                        rewrite -service_during_first_plus_later //.
                        rewrite -addn1 leq_add2l.
                        rewrite -addn1 addnC leq_add //.
                        by apply ideal_proc_model_ensures_ideal_progress.
                      }

                      have L0: 0 < service sched j (t1 + k.+1); first by apply leq_ltn_trans with (cs_start cs1).
                      apply leq_trans with (service sched j (t1 + k.+1) - 1).
                      { by rewrite -(leq_add2r 1) subn1 !addn1 prednK //. }
                      rewrite -(leq_add2r 1) subn1 addn1 prednK //.
                      rewrite /service /service_during (@big_cat_nat _ _ _ (t1 + k)) //=.
                      rewrite leq_add2l.
                      rewrite addnS big_nat1. unfold service_at.
                by apply service_at_most_one.

                      by rewrite addnS.
                    }
                  }
                  move: H_resource_locks_are_properly_nested => [[T1 T2] | [T1 T2]]; last by done.
                  by exfalso; move: NEQ1; rewrite ltnNge; move => /negP NEQ1; apply: NEQ1.
                }
                move: Ho => /andP [SCHEDo /eqP SERVo].
                move: (Hl) => /andP [SCHEDl /eqP SERVl].
                simpl in SERVo, SERVl.
                exists rl.
                intros.
                exists cs1; repeat split; try done.
                unfold section_remains_locked_at.
                exists ltl.

                have NEQ: ltl < t.
                { apply leq_trans with t1; last by move: H5 => /andP [T1 T2].
                  move: (LOCKro t1) => L. feed L.
                  { apply/andP; split; first by done.
                    move: H5 => /andP [T1 T2]. by rewrite leq_addr.
                  }
                  
                  move: L => [cs3 [IN3 [RES3 LOCK3]]].

                  have F := cannot_be_locked_twice_in_row  _ _ _ _ _ _ _ IN3 LOCK3 INo To.
                  feed_n 3 F; try done.
                  { by rewrite leq_addr //. }
                  { by rewrite RESo RES3. }
                  { intros; rewrite RES3; apply LOCKro.
                    move: H6 => /andP [T1 T2]; apply ltnW in T2.
                      by apply/andP; split.
                  }
                  subst cs3.
                  move: (LOCK3) => [lt1 [IN4 [HH1 SERV]]].
                  
                  have L := earlier_resource_locks_earlier _ _ _ _ _ Hl HH1.
                  feed L; try done.
                  
                    by apply leq_ltn_trans with lt1.
                }
                
                split; first by done.
                split; first by done.
                apply/andP; split.
                rewrite -SERVl. by apply service_monotonic, ltnW.
                apply leq_ltn_trans with (service sched j (t1 + k.+1)).
                apply service_monotonic; move: H5 => /andP [T1 T2]; by done.
                  by move: H2l => /andP [T1 T2].
              }
          Qed.

          
          (* TODO: comment *)
          Lemma resource_remains_locked_regardless_job_schedule:
            forall t1 t2 tl tu,
              t1 <= tl < t2 ->
              t1 <= tu < t2 ->
              job_scheduled_at j tl ->
              job_scheduled_at j tu ->
              (forall t, t1 <= t < t2 -> job_scheduled_at j t -> exists r, remains_locked_at j r t) ->
              (forall t, tl <= t <= tu ->                        exists r, remains_locked_at j r t).
          Proof.
            intros ? ? ? ? NEQl NEQu SCHEDl SCHEDu ALL t NEQ.
            case SCHEDt: (job_scheduled_at j t).
            { apply ALL; last by done.
              apply/andP; split.
              - by apply leq_trans with tl; [move: NEQl => /andP [T1 T2] | move: NEQ => /andP [T1 T2]].
              - by apply leq_ltn_trans with tu; [move: NEQ => /andP [T1 T2] | move: NEQu => /andP [T1 T2]]. }
            { have NEQ2: tl <= t < tu.
              { move: NEQ => /andP [T1 T2].
                apply/andP; split; first by done.
                move: T2; rewrite leq_eqVlt; move => /orP [/eqP T2|T2]; last by done.
                  by subst t; rewrite SCHEDt in SCHEDu. }
              move: NEQ NEQ2 => _ NEQ.

              have EX:
                exists t',
                  t < t' <= tu /\
                  (forall tb, t <= tb < t' -> ~~ job_scheduled_at j tb) /\
                  job_scheduled_at j t'.
              { apply exists_first_intermediate_point.
                - by apply ltnW; move: NEQ => /andP [NEQ1 NEQ2].
                - by rewrite SCHEDt.
                - by done.
              }

              move: EX => [t' [NEQ2 [NSCHED SCHED]]].
              move: (ALL t') => LOCK. feed_n 2 LOCK.
              { apply/andP; split.
                - apply leq_trans with t.
                  apply leq_trans with tl. by move: NEQl => /andP [T1 T2]. by move: NEQ => /andP [T1 T2].
                    by move: NEQ2 => /andP [T1 T2]; apply ltnW.
                - apply leq_ltn_trans with tu.  by move: NEQ2 => /andP [T1 T2]. by move: NEQu => /andP [T1 T2].
              } by done.
              move: LOCK => [r LOCK].
              
              
              exists r.

              have EX: exists k, t' = t + k.
              { exists (t' - t); rewrite subnKC. by done.
                move: NEQ2 => /andP [T1 T2].
                  by apply ltnW.
              }

              move: EX => [k EQ]; subst t'. clear NEQ2 SCHED.
              induction k.
              - by rewrite addn0 in LOCK.
              - apply IHk.
                intros. apply NSCHED. move: H5 => /andP [T1 T2]; apply/andP; split. by done.
                apply ltn_trans with (t + k). by done. by rewrite addnS.  clear IHk.
                apply lemma24; last by rewrite -addnS.
                apply NSCHED. apply/andP; split. by rewrite leq_addr. by rewrite addnS.
                
            }
          Qed.

          (* Finally we prove that for any time interval [t1, t2) the fact that the job j 
             has been scheduled more than B times inside this interval implies the existence 
             of time instant where j was scheduling without holding any resource. *)
          Lemma blocking_cannot_be_too_long :
            forall t1 t2,
              B < service_during sched j t1 t2 ->
              exists tnc,
                t1 <= tnc < t2
                /\ job_scheduled_at j tnc
                /\ current_priority_ceiling j tnc = 0.
          Proof.
            move=> t1 t2 SERV.
            have LT: t1 < t2.
            { by move_neq_up CONTR; move: SERV; rewrite /service_during big_geq ?ltn0. }
            have EQ: forall P xs, has P xs = ~~ (all (fun x => ~~ P x) xs).
            { by intros; induction xs; last rewrite //= IHxs negb_and Bool.negb_involutive. }
            have [] := incremental_service_during sched _ j t1 t2 0 => //; first by lia.
            move=> tl [NEQl [SCHEDl SERVl]].
            have [] := incremental_service_during sched _ j t1 t2 B => //.
            move=> tu [NEQu [SCHEDu SERVu]].
            

            
            have L: has (fun t => (job_scheduled_at j t)&&(current_priority_ceiling j t == 0)) (iota t1 (t2-t1)).
            { rewrite EQ; apply/negP; intros CONTR.
              move: CONTR => /allP CONTR.
              have PR: forall t, t1 <= t < t2 -> (~ job_scheduled_at j t \/ current_priority_ceiling j t > 0).
              { intros.
                feed (CONTR t); first by rewrite mem_iota subnKC; last apply ltnW.
                move: CONTR => /nandP [ALT|ALT]; [left|right].
                - by apply/negP.
                - by rewrite lt0n.
              } move: CONTR PR => _ CONTR.
              have PR: forall t, t1 <= t < t2 -> job_scheduled_at j t -> current_priority_ceiling j t > 0.
              { by intros t K SCHED; move: (CONTR t K) => [ALT|ALT]; [ exfalso | ]. }
              move: CONTR PR => _ CONTR.
              have PR: forall t, t1 <= t < t2 -> job_scheduled_at j t -> exists r, remains_locked_at j r t.
              { by intros t K SCHED; move: (CONTR t K SCHED) => CPC; apply lemma31 with (k := 0). }

              have NEQ: tl <= tu.
              { move_neq_up LTn.
                rewrite -(service_during_cat _ _ _ tu) in SERVl.
                rewrite SERVu in SERVl.
                lia. lia.
              }
              
              have PR5 := resource_remains_locked_regardless_job_schedule
                            _ _ _ _ NEQl NEQu SCHEDl SCHEDu PR.

              have PR4 := existence_of_outer_resource _ _ _ PR5.
              feed PR4; first by done.
              
              unfold critical_sections_are_bounded in H_critical_sections_are_bounded.
              move: PR4 => [r PR4].

              clear LT.
              move: (PR4 tl) => T; feed T; first by apply/andP; split.
              move: T => [cs1 [IN1 [RES1 LOCK1]]].
              move: (PR4 tu) => T; feed T; first by apply/andP; split.
              move: T => [cs2 [IN2 [RES2 LOCK2]]].

              specialize (cannot_be_locked_twice_in_row tl tu cs1 cs2) => CL.
              feed_n 7 CL; try done.
              { by rewrite RES1 RES2. }
              { intros; rewrite RES1; apply PR4.
                move: H5 => /andP [T1 T2]; apply/andP; split. by done. by apply ltnW. }
              
              rewrite -CL in LOCK2.
              move: LOCK1 => [_ [_ [_ SERl]]].
              move: LOCK2 => [_ [_ [_ SERu]]].

              
              clear EQ.
              have EQ1: service sched j tl = service sched j t1 + service_during sched j t1 tl.
              { rewrite /service /service_during -(@big_cat_nat _ _ _ t1) //=.
                  by move: NEQl => /andP [T1 T2]. }
              have EQ2: service sched j tu = service sched j t1 + service_during sched j t1 tu.
              { rewrite /service /service_during -(@big_cat_nat _ _ _ t1) //=.
                  by move: NEQu => /andP [T1 T2]. }
              rewrite EQ1 in SERl.
              rewrite EQ2 in SERu.
              set (x := service sched j t1) in *.
              move: (H_critical_sections_are_bounded _ IN1); rewrite leq_subLR; move => BOUND.
              move: BOUND; rewrite leqNgt; move => /negP BOUND; apply: BOUND.
              lia.
            }
            
            move: L => /hasP [t IN /andP [SCHED /eqP CPC]].
            exists t; split; try done.
            by move: IN; rewrite mem_iota subnKC; last apply ltnW.
          Qed.

        End BlockingLength.


        (* TODO: comment *)
        Variable B: instant.
        Hypothesis H_B_positive: B > 0.
        Hypothesis H_critical_sections_are_bounded: forall j, critical_sections_are_bounded j B.
        Hypothesis H_resource_locks_are_properly_nested: critical_sections_are_properly_nested.
        Hypothesis H_only_one_section_of_any_resource: only_one_critical_section_of_any_resource.

        (* TODO: comment *)
        Lemma priority_inversion_is_bounded:
          priority_inversion_is_bounded_by_constant arr_seq sched tsk B.
        Proof.
          move=> j ARR TASK COST t1 t2 PREF.
          have REFL : reflexive_job_priorities jlfp_policy.
          { by move => s; unfold hep_job, jlfp_policy, hep_task, NumericFPAscending, FP_to_JLFP, hep_task. } 
          have [ZERO|POS] := posnP (cumulative_priority_inversion arr_seq sched j t1 t2); first by rewrite ZERO.
          move_neq_up CONTR.
          have [jlp1 [t [NEQ [LPjlp1 SCHEDjlp1]]]]:
            exists jlp t, t1 <= t < t2 /\ jlfp_lower_priority jlp j /\ job_scheduled_at jlp t.
          { move: POS; rewrite sum_nat_gt0 => /hasP [t NEQ PI].
            have LE: t1 <= t < t2 by move: NEQ; rewrite mem_filter mem_iota subnKC; last move: PREF => [T1 T2].
            move: PI. rewrite lt0b.
            move => /uni_priority_inversion_P [] => // => [s SCHED HEP].
            by exists s, t.
          }
          have FLF2:
            forall t, t1 <= t < t2 -> job_scheduled_at jlp1 t -> ~ current_priority_ceiling jlp1 t = 0.
          { clear CONTR SCHEDjlp1 NEQ t => t NEQ SCHED PR.
            have [jhp [ARRhp [BACKhp HPhp]]]:
              exists jhp, arrives_in arr_seq jhp /\ job_backlogged_at jhp t /\ hep_job jhp j.
            { have EX := pending_hp_job_exists arr_seq _ sched _ j _ _ _ _ _ PREF t.
              feed_n 6 EX => //.
              move: EX => [jhp [ARRs [PEN HP]]].
              exists jhp; repeat split => //.
              apply/andP; split => //; apply/negP => CONTR.
              have EQ : jlp1 = jhp by apply: ideal_proc_model_is_a_uniprocessor_model => //.
              by subst jlp1; move: LPjlp1 => /negP.
            }
            have := H_respects_policy jhp jlp1 t ARRhp BACKhp SCHED.
            rewrite /current_priority PR maxn0 geq_max leqNgt => /andP [/negP PRIO _]; apply: PRIO.
            by apply: leq_trans; [apply lemma42 | apply lemma43].
          }
          have EQ:
            cumulative_priority_inversion arr_seq sched j t1 t2 = service_during sched jlp1 t1 t2.
          { rewrite /cumulative_priority_inversion /service_during.
            apply eq_big_nat => t' NEQ'; rewrite service_at_is_scheduled_at.
            have [SCHED' | NSHED] := boolP (scheduled_at sched jlp1 t').
            { by apply/eqP; rewrite eqb1; apply /uni_priority_inversion_P => //. }
            { apply/eqP; rewrite eqb0.
              apply/negP => /uni_priority_inversion_P [] => // [jlp2 SCHEDjlp2 LP].
              have L := only_one_lower_priority_job_can_block j ARR _ _ _ PREF jlp1 jlp2 t t'.
              feed_n 7 L => //; first by apply/eqP.
              by subst jlp2; rewrite SCHEDjlp2 in NSHED.
            }
          }
          rewrite EQ in CONTR.
          have [] := blocking_cannot_be_too_long jlp1 B _ _ _ _ t1 t2 => //.
          move => tnc [NEQtnc [SCHED NICS]].
          by apply FLF2 with (t := tnc).
        Qed.

      End PriorityInversionIsBounded.

      
      (** * TODO: smth *)
      (** TODO: comment *)
      (* TODO: name *)
      Section RTA.

        (* Let B a pos. const. and ... *)
        Variable B: instant.
        Hypothesis H_B_positive: B > 0.
        Hypothesis H_critical_sections_are_bounded: forall j, critical_sections_are_bounded j B.

        
        Hypothesis H_resource_locks_are_properly_nested: critical_sections_are_properly_nested.
        Hypothesis H_proper_sections: critical_sections_are_properly_formed.
        Hypothesis H_only_one_section_of_any_resource: only_one_critical_section_of_any_resource.
        
        Hypothesis H_respects_policy: respects_FP_policy_with_resources.


        (* Let L be any positive fixed point of the busy interval recurrence. *)
        Variable L : instant.
        Hypothesis H_L_positive : L > 0.
        Hypothesis H_fixed_point : L = B + total_hep_rbf L.

        (* Let's define the notion of search space for clarity. *)
        Let is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).

        (* Next, consider any value R, and assume that for any given
           arrival A from search space there is a solution of the
           response-time bound recurrence which is bounded by R. *)
        Variable R : duration.
        Hypothesis H_R_is_maximum :
          forall A,
            is_in_search_space A ->
            exists F,
              B + task_rbf (A + ε) + total_ohep_rbf (A + F) <= A + F /\
              F <= R.

        (* TODO: comment *)
        (* TODO: name *)
        Lemma uniprocessor_response_time_bound :
          task_response_time_bound arr_seq sched tsk R.
        Proof.
          eapply uniprocessor_response_time_bound_fp with (L := L) => //=.
          - by apply priority_inversion_is_bounded.
          - rewrite !subnn => A PI.
            edestruct H_R_is_maximum as [F [EQ1 EQ2]] => //=.
            by exists F; split; [rewrite subn0 | rewrite addn0].
        Qed.

      End RTA.

    End Analysis.
    
  End Locks.

  (* ==> Closed under the global context *)
  Print Assumptions uniprocessor_response_time_bound.
