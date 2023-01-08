Require Import rt.util.all.
Require Import rt.model.arrival.basic.job
               rt.model.arrival.basic.task_arrival
               rt.model.priority.
Require Import rt.model.schedule.uni.service
               rt.model.schedule.uni.workload
               rt.model.schedule.uni.schedule
               rt.model.schedule.uni.response_time.
Require Import rt.model.schedule.uni.limited.platform
               rt.model.schedule.uni.limited.schedule
               rt.model.schedule.uni.limited.busy_interval
               rt.model.schedule.uni.limited.rbf
               rt.model.schedule.uni.limited.fixed_priority.fp_rta_theory.
Require Import rt.model.arrival.curves.bounds. 
Require Import rt.analysis.uni.arrival_curves.workload_bound.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * In this file we ... *)
(* TODO: comment *)
(* In this section we ... *) 
Module Locks.
  
  Import Epsilon Job ArrivalCurves TaskArrival Priority  UniprocessorSchedule Workload Service ResponseTime
         MaxArrivalsWorkloadBound LimitedPreemptionPlatform RBF
          AbstractRTAforFPwithArrivalCurves. 

  (** TODO: name *) 
  Section Locks.

    Context {Task: eqType}.
    Variable task_cost: Task -> time.    
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (* TODO: better comment *)
    (* Opaque type of resource. *)
    Context {Resource: eqType}.
    Context {CriticalSection: eqType}.

    (* To each job we assign a set of critical sections. *)
    Variable job_critical_sections: Job -> seq CriticalSection.
    
    (* Given some critical sections *)
    Variable cs_start: CriticalSection -> time.
    Variable cs_end: CriticalSection -> time.
    Variable cs_resource: CriticalSection -> Resource.

    
    (* Let rs be a set of all available resources. *)
    Variable rs: seq Resource.

    (* Suppose there is a function that maps each task to a set 
       of resources that this task can use. *)
    Variable task_res: Task -> seq Resource.

    (* We define a type of critical_section, which is a pair of a resource 
       and a time interval in which this resource is locked. *)
    (* Definition critical_section: Type := (Resource * (time * time)). *)

    
    (* Priority Type. *)
    Let Prio: Type := nat.

    (* Priority is just a natural number. *) 
    Variable task_prio: Task -> Prio.
    Let job_prio j := task_prio (job_task j).

    (* Skip it for now *)
    (* TODO: fix, del? *)
    Let task_blocking := fun (task: Task) => 10.
    Let job_blocking := fun (job: Job) => 10.

    (* Skip it for now *)
    (* TODO: del? *)
    Let task_last (task: Task) := ε.
    Let job_last (job: Job) := ε.

    (* Consider any arrival sequence with consistent, non-duplicate arrivals... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* TODO: del *)
    (* ... in which jobs are correct segmented jobs. *)
    (* Hypothesis H_valid_segmented_job:
      forall j,
        arrives_in arr_seq j ->
        valid_segmented_task_job
          job_blocking job_last job_cost task_blocking task_last task_cost job_task j. *)

    (* Next, consider any uniprocessor schedule of this arrival sequence...*)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* Assume we have sequential jobs. *)
    Hypothesis H_sequential_jobs: sequential_jobs job_arrival job_cost sched job_task.

    (* TODO: comment *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.

    (* ... where jobs do not execute before their arrival nor after completion. *)
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* TODO: comment. *)
    Let higher_eq_priority: FP_policy Task :=
      fun task1 task2 => task_prio task1 >= task_prio task2.
    Let lower_priority task1 task2 := ~~ higher_eq_priority task1 task2.
 
    Let jlfp_higher_eq_priority := FP_to_JLFP job_task higher_eq_priority.
    Let jlfp_lower_priority := FP_to_JLFP job_task lower_priority.
    
    (* Consider a task set ts... *)
    Variable ts: list Task. 
    (* ...and assume that it is correct in sense of segmented tasks. *)
    (* Hypothesis H_valid_ts: valid_segmented_taskset task_blocking task_last task_cost ts. *)

    (* Let tsk be any task in ts. *) 
    Variable tsk: Task.
    Hypothesis H_tsk_in_ts: tsk \in ts.
    
    (* Assume that a job cost cannot be larger than a task cost... *)
    Hypothesis H_job_cost_le_task_cost:
      forall j,
        arrives_in arr_seq j ->
        job_cost_le_task_cost task_cost job_cost job_task j.

    (* Next, we assume that all jobs come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* TODO: del *)
    Hypothesis H_job_pos:
      forall j, job_task j = tsk -> 0 < job_cost j.
    
    (* Let max_arrival be any task arrival bound. *)
    Variable max_arrivals: Task -> time -> nat.
    Hypothesis H_is_arrival_bound:
      forall tsk, tsk \in ts -> is_arrival_bound job_task arr_seq max_arrivals tsk.

    (* Let's define some local names for clarity. *)
    Let task_rbf := task_request_bound_function task_cost max_arrivals tsk.
    Let total_hep_rbf :=
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.
    Let total_ohep_rbf :=
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk.

    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_arrival job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let job_backlogged_at := backlogged job_arrival job_cost sched.
    Let arrivals_between := jobs_arrived_between arr_seq.
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched.
    
    (** * Definitions *)
    (* In this section we ... *)
    Section Definitions.

      (* TODO: comment *)
      Section DefinitionsRelatedToCriticalSection.

        (* We define a predicate which says if task tsk uses a resource r. *)
        Definition task_uses_resource (tsk: Task) (r: Resource) := r \in task_res tsk.

        (* TODO: check comment *)
        (* We say that job j locks a critical section r at time t, if job j was scheduled 
           at time t, and service of j at time t is equal to lock time of the critical section r. *)
        Definition locks_at (j: Job) (cs: CriticalSection) (t: time) :=
          (job_scheduled_at j t) && (service sched j t == cs_start cs).

        (* TODO: check comment *)
        (* We say that a critical section res remains locked by a job j at a time t if there 
           is a time moment lock_time < t in which the critical section was locked by j 
           and the critical section is still not unlocked. *)
        Definition section_remains_locked_at (j: Job) (cs: CriticalSection) (t: time) :=
          exists lock_time,
            lock_time < t /\
            locks_at j cs lock_time /\
            cs_start cs <= service sched j t < cs_end cs.

        (* TODO: check comment *)
        (* We also introduce a computable version of section_remains_locked_at notion. *)
        Definition section_remains_locked_at_comp (j: Job) (cs: CriticalSection) (t: time) :=
          has (fun lock_time => (locks_at j cs lock_time) && ( cs_start cs <= service sched j t <  cs_end cs)) (iota 0 t).

        (* TODO: check comment *)
        (* Next we introduce the notion of being locked for a resource. We say that the 
           resource r is locked by a job j at a time t, if there is a critical section 
           which contains resource r and (is??) locked at time t.  *)
        Definition remains_locked_at (j: Job) (r: Resource) (t: time) :=
          exists cs: CriticalSection,
            (cs \in job_critical_sections j) /\
            (cs_resource cs = r) /\
            section_remains_locked_at j cs t.

        (* TODO: check comment *)
        (* We also introduce a computable version of remains_locked_at notion. *)
        Definition remains_locked_at_comp (j: Job) (r: Resource) (t: time) :=
          has (fun css => section_remains_locked_at_comp j css t && (cs_resource css == r) ) (job_critical_sections j).
        
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
        Definition critical_sections_are_bounded (j: Job) (B: time) :=
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
        Definition priority_ceiling (r: Resource): Prio :=
          \max_(tsk <- ts | task_uses_resource tsk r) (task_prio tsk).
       
        (* We define the current priority ceiling for a job j at time t, which is 
           equal to the maximum of resource priority that is locked by the job 
           j at time t. In case when there is no locked resource current 
           priority ceiling is equal to zero. *)
        Definition current_priority_ceiling (j: Job) (t: time): Prio :=
          \max_(r <- rs | (fun r => remains_locked_at_comp j r t) r) (priority_ceiling r).
        
        (* Finally, we can define current priority for a job j at a moment of time t. It is
           equal to the maximun between job priority and current priority ceiling of the job. *)
        Definition current_priority (j: Job) (t: time): Prio :=
          maxn (job_prio j) (current_priority_ceiling j t).
        
        (* Next, we describe hypotheses for the current model. 
           We say that an FP policy is respected by the schedule iff a scheduled task has 
           higher (or same) current priority than any backlogged job. *)
        Definition respects_FP_policy_with_resources :=
          forall j j_hp t,
            arrives_in arr_seq j ->
            backlogged job_arrival job_cost sched j t ->
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
          intros; apply: (iffP idP); intros.
          { move: H => /hasP [lt IN /andP [H1 H2]].
            exists lt; repeat split; try done.
              by move: IN; rewrite mem_iota add0n; move => /andP [_ H].
          }
          { move: H => [lt [IN [LOCK SERV]]].
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
          intros; apply: (iffP idP); intros.
          { move: H => /hasP [cs IN /andP [SEC /eqP RES]].
            exists cs; repeat split; try done.
              by apply/section_remains_locked_atP.
          }
          { move: H => [cs [IN [RES LOCK]]]. 
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
            arrives_in arr_seq j2 -> (* TODO: del? *)
            job_pending_at j1 t ->
            job_pending_at j2 t ->
            current_priority j1 t < current_priority j2 t ->
            job_backlogged_at j1 t.
        Proof.
          intros j1 j2 t ARR PEND1 PEND2 PRIO.
          have NEQ: j1 <> j2.
          { intros CONTR; subst j2.
              by rewrite ltnn in PRIO. }
          apply/negPn/negP; intros NBACK.
          move: NBACK; rewrite negb_and Bool.negb_involutive; move => /orP [NPEND1 | NN].
          { by exfalso; move: NPEND1 => /negPn NPEND1; apply: NPEND1. }
          move: PRIO; rewrite ltnNge; move => /negP PRIO; apply: PRIO.
          apply H_respects_policy; try done.
          apply/andP; split; first by done.
          apply/negP; intros SCHED; apply: NEQ.
            by eapply only_one_job_scheduled; eauto 2.
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
          Variable t: time.

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
              - by apply ltn_trans with t.
              - by apply leq_trans with (service sched j t); last apply service_monotonic. 
              - apply leq_ltn_trans with (service sched j t); last by done.
                rewrite /service /service_during (@big_cat_nat _ _ _ t) //= big_nat1.
                rewrite -{2}[\sum_(0 <= t0 < t) service_at sched j t0]addn0 leq_add2l.
                  by rewrite leqn0 /service_at eqb0.
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
                  by rewrite leqn0 /service_at eqb0.
              - by apply leq_ltn_trans with (service sched j t.+1); first apply service_monotonic. 
            }
          Qed. 

          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma20:
            current_priority_ceiling j t = current_priority_ceiling j t.+1.
          Proof.
            apply lemma23.
            - intros r IN LOCK.
              exists r; repeat split; try done.
              move: LOCK => /remains_locked_atP LOCK; apply/remains_locked_atP.
                by apply lemma24 in LOCK.
            - intros r IN LOCK.
              exists r; repeat split; try done.
              move: LOCK => /remains_locked_atP LOCK; apply/remains_locked_atP.
                by apply lemma24.            
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
          Variable t: time.

          (* TODO: comment *)
          Variable k: nat.

          (* TODO: comment *)
          Hypothesis H_priority_ceiling_is_large_enough: k < current_priority_ceiling j t.

          
          (* TODO: comment *)
          (* TODO: name *)
          Lemma lemma31:
            exists r, remains_locked_at j r t.
          Proof.
            apply leq_ltn_trans with (m := 0) in H_priority_ceiling_is_large_enough; last by done.
            apply lemma25 in H_priority_ceiling_is_large_enough.
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
              by rewrite lt0b.
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
                by apply/eqP/eqP; rewrite neq_ltn; apply/orP; left.
          Qed.            
          
          (* TODO: comment *)
          (* CHECK: locking? *)
          Lemma moment_of_locking_exists:
            exists rc,
              rc < t /\
              job_scheduled_at j rc /\
              current_priority_ceiling j rc <= k /\
              (forall x, rc < x <= t -> k < current_priority_ceiling j x).
          Proof. 
            move: H_priority_ceiling_is_large_enough => CPC; clear H_priority_ceiling_is_large_enough.
            induction t.
            - have POSt: 0 < current_priority_ceiling j 0; first by apply leq_ltn_trans with k.
              exfalso. move: POSt; rewrite lt0n; move => /negP POSt; apply: POSt.
              rewrite /current_priority_ceiling big1 //.
              move => r /remains_locked_atP [_ [_ [_ [lt [LT _]]]]].
                by rewrite ltn0 in LT. 
            - case GTLE: (k < current_priority_ceiling j t0). 
              { move: (IHt0 GTLE) => [lt [LT [SCHED [ZERO P]]]].
                exists lt; repeat split; try done.
                - by apply ltn_trans with t0.
                - move => x /andP [H1 H2].
                  move: H2; rewrite leq_eqVlt; move => /orP [/eqP H2|H2]; [by subst x | ].
                    by apply P; apply/andP; split; last rewrite -ltnS.
              }
              { move: GTLE => /negP/negP; rewrite -leqNgt; move => LT.
                exists t0; repeat split; try done.
                - apply negbNE; apply/negP; intros CONTR.
                  apply lemma20 in CONTR.
                  move: CPC; rewrite -CONTR ltnNge; move => /negP CPC.
                    by apply CPC.
                - move => x /andP [NEQ1 NEQ2].
                  have EQ: x = t0.+1; first by apply/eqP; rewrite eqn_leq; apply/andP; split.
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
        (* In this section we prove a property that says that normal(?) priority 
           and ceiling priority of one job don't overlap with priorities for another job.
           More formal, suppose there are two jobs j1 j2. Next, let them hold some resource
           at some time t, so both of them have raised priority (due to ceiling). 
           Then we can prove that either normal priority of job j1 is not smaller that
           ceiled priotiry of job j2, or vice versa. *)
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
            Variable t: time.

            (* TODO: comment *)
            (* TODO: name *)
            Hypothesis H_ceiling_of_j1_is_active: job_prio j1 < current_priority_ceiling j1 t.
            Hypothesis H_ceiling_of_j2_is_active: job_prio j2 < current_priority_ceiling j2 t.

            (* TODO: names *)
            (* TODO: comment *)
            (* We can prove that there exists ... *)
            Variables t_j1: time.
            Hypothesis EX1: job_scheduled_at j1 t_j1 /\ service sched j1 t_j1 = 0.

            (* TODO: comment *)
            Variable t_j2: time.
            Hypothesis EX2: job_scheduled_at j2 t_j2 /\ service sched j2 t_j2 = 0.

            (* TODO: comment *)
            Hypothesis LTj1j2: t_j1 < t_j2.

            (* TODO: comment *)
            Variable rc1: time.
            Hypothesis N1 : rc1 < t.
            Hypothesis SCHEDrc1 : job_scheduled_at j1 rc1.
            Hypothesis PRIOrc1 : current_priority_ceiling j1 rc1 <= job_prio j1.
            Hypothesis PRIO2c1 : forall x : time, rc1 < x <= t -> job_prio j1 < current_priority_ceiling j1 x.

            (* TODO: comment *)
            Variable rc2: time. 
            Hypothesis N2: rc2 < t.
            Hypothesis SCHEDrc2: job_scheduled_at j2 rc2.
            Hypothesis PRIOrc2: current_priority_ceiling j2 rc2 <= job_prio j2.
            Hypothesis PRIO2c2: forall x: time, rc2 < x <= t -> job_prio j2 < current_priority_ceiling j2 x.
            

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
                by rewrite /service_at lt0b. 
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
                by rewrite /service_at lt0b. 
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
              { by intros x SC1 SC2; eapply H_not_equal, only_one_job_scheduled; eauto 2. }
              have FBACK: forall t, job_pending_at j1 t -> job_scheduled_at j2 t -> job_backlogged_at j1 t.          
              { intros x PEND SCHED.
                apply/andP; split; first by done.
                apply/negP; intros SCHED2.
                  by move: (OOJS _ SCHED2 SCHED).
              }
              apply leq_trans with (current_priority j2 rc2).
              - apply H_respects_policy; try done.
                + by eapply H_jobs_come_from_arrival_sequence; eauto 2. 
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
              { by intros x SC1 SC2; eapply H_not_equal, only_one_job_scheduled; eauto 2. }
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
              
              intros x H.
              have EX: exists k, x = rc2 + k.
              { by exists (x - rc2); rewrite subnKC; last move: H => /andP [H _]. } move: EX => [k EQ].
              subst x. 
              induction k.
              - by rewrite addn0; apply F1. 
              - feed IHk.
                { apply/andP; split.
                  - by rewrite leq_addr.
                  - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: H => /andP [_ H]].
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
                    - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: H => /andP [_ H]].       
                  }
                  apply lemma17 with j2; try done.
                  apply PEND1; try done.
                  { apply/andP; split.
                    - by apply leq_trans with rc2; last rewrite leq_addr.
                    - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: H => /andP [T1 T2]].
                  }
                  apply PEND2; try done.
                  { apply/andP; split.
                    - by apply leq_trans with rc2; last by rewrite leq_addr.
                    - by apply leq_trans with (rc2 + k.+1); [rewrite addnS | move: H => /andP [T1 T2]].
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
              { by intros x SC1 SC2; eapply H_not_equal, only_one_job_scheduled; eauto 2. }
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
                { intros; apply ALL.
                  move: H => /andP [T1 T2].
                  apply/andP; split; first by done.
                    by apply ltn_trans with (t1 + k); last rewrite addnS.
                } 
                rewrite IHk.
                rewrite addnS; apply lemma38.
                specialize (ALL (t1+k)); feed ALL.
                { by apply/andP; split; [rewrite leq_addr | rewrite addnS]. }
                  by move: ALL => /andP [_ NSCHED].
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
              { by intros x SC1 SC2; eapply H_not_equal, only_one_job_scheduled; eauto 2. }
              
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
            Variable t: time.

            (* TODO: comment *)
            Hypothesis CPC1: job_prio j1 < current_priority_ceiling j1 t.
            Hypothesis CPC2: job_prio j2 < current_priority_ceiling j2 t.
            
            (* TODO: comment *)
            Lemma ceiling_property:
              current_priority_ceiling j1 t <= job_prio j2
              \/ current_priority_ceiling j2 t <= job_prio j1.
            Proof.
              have UT1: forall t, job_scheduled_at j1 t -> job_scheduled_at j2 t -> False.
              { by intros x SC1 SC2; eapply H_not_equal, only_one_job_scheduled; eauto 2. }
              have EX1: exists j1a, job_scheduled_at j1 j1a /\ service sched j1 j1a = 0.
              { apply lemma37 in CPC1.
                apply lemma32 in CPC1.
                move: CPC1 => [j1a [_ [SCHED SERV]]].
                exists j1a; repeat split; try done.
              } 
              have EX2: exists j2a, job_scheduled_at j2 j2a /\ service sched j2 j2a = 0.
              { apply lemma37 in CPC2.
                apply lemma32 in CPC2.
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
          Variable t1 t2: time.
          Hypothesis H_busy_interval_prefix:
            busy_interval_prefix job_arrival job_cost job_task arr_seq sched higher_eq_priority tsk j t1 t2.

          (* In this section we prove that a job with a lower priority should raise 
             priority (= lock some resource) in order to execute inside busy interval. *)
          Section LowerPriorityJobShouldRaisePriority.

            (* TODO: comment *)
            Variable t: time.
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
                  jlfp_higher_eq_priority jhp j.
              { intros.
                have P := pending_hp_job_exists
                            job_arrival job_cost job_task arr_seq _ sched higher_eq_priority
                            tsk j _ _ _ _ _ t1 t2 _ _ t.
                feed_n 9 P; try done.
                { by unfold FP_is_reflexive, reflexive, higher_eq_priority. }
                { by intros s ARRs; move: (H_valid_segmented_job _ ARRs) => [[POS _] _]. }
                move: P => [jhp [ARR [PEN HP]]].
                exists jhp; repeat split; try done.
                intros EQ; subst jlp.
                unfold jlfp_higher_eq_priority in *.
                unfold jlfp_lower_priority, lower_priority, FP_to_JLFP in *.
                rewrite H_job_of_tsk HP in LP. by done.
                apply/andP; split; first by done.
                apply/negP; intros CONTR.
                have OK:= only_one_job_scheduled _ _ _ _ SCHED CONTR; subst jlp.
                unfold jlfp_higher_eq_priority in *.
                unfold jlfp_lower_priority, lower_priority, FP_to_JLFP in *.
                rewrite H_job_of_tsk HP in LP. by done. 
                  by rewrite /jlfp_higher_eq_priority /FP_to_JLFP H_job_of_tsk.
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
                - by rewrite /jlfp_lower_priority /FP_to_JLFP /lower_priority /higher_eq_priority -ltnNge in LP.
                - by rewrite /jlfp_higher_eq_priority /FP_to_JLFP /lower_priority /higher_eq_priority in HP.
              }
                by done.
            Qed.
            
            (* TODO: comment *)
            Lemma lp_job_cannot_be_scheduled_inside_busy_interval:
              current_priority jlp t1 < job_prio j ->
              ~~ job_scheduled_at jlp t.
            Proof.
              intros PRIO.

              have helper:
                forall t,
                  t1 <= t < t2 ->
                  current_priority jlp t < job_prio j -> 
                  ~~ job_scheduled_at jlp t.
              { clear H_t_inside_busy_interval PRIO t; intros t NEQ PRIO.
                case PEND: (job_pending_at jlp t). 
                - have EX := pending_hp_job_exists
                               job_arrival job_cost job_task arr_seq _ sched
                               higher_eq_priority tsk j _ _ _ _ _ _ _ H_busy_interval_prefix _ t.
                  feed_n 8 EX; try done. 
                  { by rewrite /FP_is_reflexive /reflexive /higher_eq_priority. }
                  { by intros s ARRs; move: (H_valid_segmented_job _ ARRs) => [[POS _] _]. } 
                  move: EX => [jhp [ARR [PEN HP]]].
                  move: (lemma17 H_respects_policy _ _ _ ARR PEND PEN) => BACK.
                  feed BACK.
                  { apply leq_trans with (job_prio j); first by done.
                    rewrite /higher_eq_priority in HP.
                    rewrite /current_priority leq_max; apply/orP; left.
                      by rewrite /job_prio H_job_of_tsk.
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
              move: SCHED => /negPn /negP SCHED; apply: SCHED.
              apply lp_job_cannot_be_scheduled_inside_busy_interval.
              rewrite gtn_max; apply/andP; split; last by done.
                by move: H_lower_priority; rewrite /jlfp_lower_priority /FP_to_JLFP /lower_priority -ltnNge /job_prio.
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
                  by move: LP1; rewrite /jlfp_lower_priority /FP_to_JLFP /lower_priority /higher_eq_priority -ltnNge.
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
                  by move: LP2; rewrite /jlfp_lower_priority /FP_to_JLFP /lower_priority /higher_eq_priority -ltnNge.
              }
              apply lp_job_cannot_be_scheduled_inside_busy_interval with (t := t'') in PRIO2; try done.
                by move: PRIO2 => /negP PRIO2; apply: PRIO2. 
            }          
            move: INCS1 INCS2 INCS3 INCS4 => _ _ INCS1 INCS2.
            move: (lp_job_can_be_scheduled_inside_busy_interval_only_with_raised_priority _ NEQ1 _ LP1 SCHED1) => PRIO1.
            move: (lp_job_can_be_scheduled_inside_busy_interval_only_with_raised_priority _ NEQ2 _ LP2 SCHED2) => PRIO2.
            move: (ceiling_property jlp1 jlp2 NEQ t1) => KEK.
            feed_n 2 KEK; try done.
            move: KEK => [H|H]; exfalso.
            - exfalso.
              apply leq_trans with (m := job_prio j) in H; last by done.
              move: LP2; unfold jlfp_lower_priority,FP_to_JLFP,lower_priority,higher_eq_priority; move => /negP LP2.
                by apply LP2.
            - exfalso.
              apply leq_trans with (m := job_prio j) in H; last by done.
              move: LP1; unfold jlfp_lower_priority, FP_to_JLFP,lower_priority,higher_eq_priority; move => /negP LP1.
                by apply LP1.
          Qed.
          
        End OnlyOneLowerPriorityJobCanCauseBlocking.

        (** Blocking length is bounded. *)
        (* TODO: comment *)
        Section BlockingLength.

          (* TODO: comment *)
          Variable j: Job.

          (* TODO: comment *)
          Variable B: time.
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
                by rewrite /service_at lt0b.
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
                { rewrite /service /service_during [X in _<X](@big_cat_nat _ _ _ lt2) //=; last by rewrite ltnW.
                  rewrite -addn1 leq_add2l.
                  rewrite (big_rem lt2) //=; last first.
                  { by rewrite mem_iota; apply/andP; last rewrite subnKC // ltnW. }
                  apply leq_trans with (service_at sched j lt2); last by rewrite leq_addr.
                    by rewrite lt0b.
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
                unfold service_at.
                  by case (scheduled_at). 
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
                  move: H => /andP [T1 T2].
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
            intros ? ? LE H.
            have EX: exists k, t2 = t1 + k.
            { by exists (t2 - t1); rewrite subnKC. }
            move: EX => [k EQ]; subst t2; clear LE.
            induction k.
            - feed (H t1); first by rewrite addn0; apply/andP; split. 
              move: H => [r HLB].
              exists r; intros.
                by move: H; rewrite addn0 -eqn_leq; move => /eqP H; subst t.
            - feed IHk.
              { move => t /andP [T1 T2].
                apply H; apply/andP; split; first by done.
                apply leq_trans with (t1 + k); first by done.
                  by rewrite addnS.
              } 
              feed (H (t1 + k.+1)).
              { by apply/andP; split; first rewrite leq_addr //. } 
              move: H => [rl LOCKrl].
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
                        rewrite /service /service_during [X in _<X](@big_cat_nat _ _ _ ltl) //=; last by rewrite ltnW.
                        rewrite -addn1 leq_add2l.
                        rewrite (big_rem ltl) //=; last first.
                        { by rewrite mem_iota; apply/andP; last rewrite subnKC // ltnW. }
                        apply leq_trans with (service_at sched j ltl); last by rewrite leq_addr.
                          by rewrite lt0b.
                      }
                      have L0: 0 < service sched j (t1 + k.+1); first by apply leq_ltn_trans with (cs_start cs1). 
                      apply leq_trans with (service sched j (t1 + k.+1) - 1).
                      { by rewrite -(leq_add2r 1) subn1 !addn1 prednK //. }
                      rewrite -(leq_add2r 1) subn1 addn1 prednK //.
                      rewrite /service /service_during (@big_cat_nat _ _ _ (t1 + k)) //=.
                      rewrite leq_add2l.
                      rewrite addnS big_nat1. unfold service_at. by case (scheduled_at).
                        by rewrite addnS.
                    }
                  }
                  move: H_resource_locks_are_properly_nested => [[H1 H2] | [H1 H2]]; last by done.
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
                { apply leq_trans with t1; last by move: H => /andP [T1 T2].
                  move: (LOCKro t1) => L. feed L.
                  { apply/andP; split; first by done.
                    move: H => /andP [T1 T2]. by rewrite leq_addr.
                  }
                  
                  move: L => [cs3 [IN3 [RES3 LOCK3]]].

                  have F := cannot_be_locked_twice_in_row  _ _ _ _ _ _ _ IN3 LOCK3 INo To.
                  feed_n 3 F; try done.
                  { by rewrite leq_addr //. }
                  { by rewrite RESo RES3. }
                  { intros; rewrite RES3; apply LOCKro.
                    move: H0 => /andP [T1 T2]; apply ltnW in T2.
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
                apply service_monotonic; move: H => /andP [T1 T2]; by done.
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
              { apply AbsL.
                - by apply ltnW; move: NEQ => /andP [NEQ1 NEQ2].
                - by rewrite SCHEDt.
                - by done. }

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
                intros. apply NSCHED. move: H => /andP [H1 H2]; apply/andP; split. by done.
                apply ltn_trans with (t + k). by done. by rewrite addnS.  clear IHk.
                apply lemma24; last by rewrite -addnS.
                apply NSCHED. apply/andP; split. by rewrite leq_addr. by rewrite addnS.
                
            }
          Qed.


          (* Finally we prove that for any time interval [t1, t2) the fact that the job j 
             has been scheduled more than B times inside this interval implies the existence 
             of time instant where j was scheduling without holding any resource. *)
          Lemma blocking_cannot_be_too_long: 
            forall t1 t2,
              B < service_during sched j t1 t2 ->
              exists tnc,
                t1 <= tnc < t2 /\
                job_scheduled_at j tnc /\ 
                current_priority_ceiling j tnc = 0.
          Proof.  
            intros t1 t2 SERV.
            have LT: t1 < t2.
            { rewrite ltnNge; apply/negP; intros CONTR.
                by move: SERV; rewrite /service_during big_geq ?ltn0. 
            }
            have EQ: forall P xs, has P xs = ~~ (all (fun x => ~~ P x) xs).
            { intros.
              induction xs.
              - by done. 
              - by simpl; rewrite IHxs negb_and Bool.negb_involutive.
            }

            move: (lemma32 sched j t1 t2 0) => EX.
            feed EX; first by apply leq_ltn_trans with B.
            move: EX => [tl [NEQl [SCHEDl SERVl]]]. 

            move: (lemma32 sched j t1 t2 B) => EX.
            feed EX; first by apply leq_ltn_trans with B.
            move: EX => [tu [NEQu [SCHEDu SERVu]]].
            
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
              { by intros; move: (CONTR t H) => [ALT|ALT]; [ exfalso | ]. } move: CONTR PR => _ CONTR.
              have PR: forall t, t1 <= t < t2 -> job_scheduled_at j t -> exists r, remains_locked_at j r t.  
              { by intros; move: (CONTR t H H0) => CPC; apply lemma31 with (k := 0). } 

              
              have NEQ: tl <= tu.
              { rewrite leqNgt; apply/negP; intros LTn.
                rewrite (millionofutillemmas.LemmasToAddToCoreOfProsa.service_during_cat _ _ tu) in SERVl.
                rewrite SERVu in SERVl.
                move: SERVl => /eqP; rewrite addn_eq0; move => /andP [/eqP EQn _].
                  by move: (H_B_positive); rewrite EQn.

                  apply/andP; split. by move: NEQu => /andP [T1 T2].  by apply ltnW. 
              }
              

              have PR5 := resource_remains_locked_regardless_job_schedule _ _ _ _ NEQl NEQu SCHEDl SCHEDu PR.

              have PR4 := existence_of_outer_resource _ _ _ PR5.
              feed PR4; first by done. 
              
              unfold critical_sections_are_bounded in H_critical_sections_are_bounded.
              move: PR4 => [r PR4].

              clear LT.          
              move: (PR4 tl) => T; feed T; first by apply/andP; split.
              move: T => [cs1 [IN1 [RES1 LOCK1]]].
              move: (PR4 tu) => T; feed T; first by apply/andP; split.
              move: T => [cs2 [IN2 [RES2 LOCK2]]].
              
 
              specialize (cannot_be_locked_twice_in_row tl tu cs1 cs2) => H.
              feed_n 7 H; try done.
              { by rewrite RES1 RES2. }
              { intros; rewrite RES1; apply PR4. 
                move: H0 => /andP [T1 T2]; apply/andP; split. by done. by apply ltnW. }
              
              rewrite -H in LOCK2. 
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
              move: SERl; rewrite SERVl addn0; move => /andP [N1 N2].
              move: SERu; rewrite SERVu; move => /andP [N3 N4].
              move: BOUND; rewrite leqNgt; move => /negP BOUND; apply: BOUND.
                by apply leq_ltn_trans with (x + B); first rewrite leq_add2r.
            }
            move: L => /hasP [t IN /andP [SCHED /eqP CPC]].
            exists t; split; try done.
              by move: IN; rewrite mem_iota subnKC; last apply ltnW.
          Qed. 

        End BlockingLength.

        (** Some Nmae *)
        (* TODO: comment *)
        Variable B: time.
        Hypothesis H_B_positive: B > 0.
        Hypothesis H_critical_sections_are_bounded: forall j, critical_sections_are_bounded j B.
        Hypothesis H_resource_locks_are_properly_nested: critical_sections_are_properly_nested.
        Hypothesis H_only_one_section_of_any_resource: only_one_critical_section_of_any_resource.
        
        (* TODO: comment *)
        Lemma priority_inversion_is_bounded:
          is_priority_inversion_bound
            job_arrival job_cost job_task arr_seq sched
            higher_eq_priority tsk B.
        Proof.  
          intros j ARR TASK t1 t2 PREF. 
          have ALT: forall n, n = 0 \/ n > 0.
          { clear; intros n.
              by destruct n; [left | right ]. }
          
          move: (ALT (cumulative_priority_inversion job_task sched higher_eq_priority j t1 t2)) => [ZERO | POS].
          rewrite ZERO; by done.
          clear ALT; rewrite leqNgt; apply/negP; intros CONTR.
          
          have EX:
            exists (jlp: Job) (t: time), 
              t1 <= t < t2 /\
              jlfp_lower_priority jlp j /\
              job_scheduled_at jlp t.
          { move: POS => /sum_seq_gt0P [t [NEQ PI]].
            rewrite mem_iota subnKC in NEQ; last first.
            apply ltnW; by move: PREF => [H1 H2].
            rewrite lt0b in PI.
            unfold BusyIntervalFP.is_priority_inversion in PI.
            move: PI; case SCHED: (sched t) => [jlp | ]; last by done.
            move: SCHED => /eqP SCHED.
            case HP: (~~ jlfp_higher_eq_priority jlp j); last by done.
            move => _.
            exists jlp, t.
            repeat split; try done.
          }
          move: EX => [jlp1 [t [NEQ [LPjlp1 SCHEDjlp1]]]].
          
          have EQ:
            cumulative_priority_inversion job_task sched higher_eq_priority j t1 t2 =
            \sum_(t1 <= t < t2) job_scheduled_at jlp1 t. 
          { rewrite /job_scheduled_at /scheduled_at.
            unfold cumulative_priority_inversion, BusyIntervalFP.is_priority_inversion in *.
            apply/eqP; rewrite eqn_leq; apply/andP; split.
            { rewrite [in X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond.
              rewrite leq_sum //.
              move => t' /andP [NEQ' _].
              case SCHEDjlp2: (sched t') => [jlp2 | ]; last by done.
              case HP: (~~ jlfp_higher_eq_priority jlp2 j); last by done.
              simpl; rewrite lt0b eq_sym.
              move: SCHEDjlp2 => /eqP SCHEDjlp2.
              have L := only_one_lower_priority_job_can_block j ARR TASK _ _ PREF jlp1 jlp2 t t'.
              feed_n 6 L; try done. 
                by subst jlp2.
            }
            { rewrite [in X in X <= _]big_nat_cond [in X in _ <= X]big_nat_cond.
              rewrite leq_sum //.
              move => t' /andP [NEQ' _].
              case SCHED: (sched t') => [j' | ]; last by done.
              case EQ: (Some j' == Some jlp1); last by done.
              move: EQ => /eqP EQ; inversion EQ; subst j'.
              simpl. rewrite lt0b.

                by unfold jlfp_lower_priority, lower_priority, FP_to_JLFP in *.
                
            }   
          }
          
          have EX:
            forall t,
              t1 <= t < t2 ->
              job_scheduled_at jlp1 t ->
              exists jhp,
                jhp <> jlp1 /\
                arrives_in arr_seq jhp /\
                job_backlogged_at jhp t /\
                jlfp_higher_eq_priority jhp j.
          {
            clear SCHEDjlp1 EQ NEQ t CONTR.
            intros t NEQ SCHED.
            have EX := pending_hp_job_exists
                         job_arrival job_cost job_task arr_seq _ sched
                         higher_eq_priority tsk j _ _ _ _ _ _ _ PREF _ t.  
            feed_n 8 EX; try done.
            { by rewrite /FP_is_reflexive /reflexive /higher_eq_priority. }
            { by intros s ARRs; move: (H_valid_segmented_job _ ARRs) => [[T _] _]. }
            move: EX => [jhp [ARRhp [PEN HP]]].
            exists jhp; repeat split; try done.
            intros EQ; subst jlp1.
            unfold jlfp_higher_eq_priority in *.
            unfold jlfp_lower_priority, lower_priority, FP_to_JLFP in *.
              by rewrite TASK HP in LPjlp1.
              
              apply/andP; split; first by done.
              apply/negP; intros CONTR.
              have OK:= only_one_job_scheduled _ _ _ _ SCHED CONTR; subst jlp1.
              
              unfold jlfp_higher_eq_priority in *.
              unfold jlfp_lower_priority, lower_priority, FP_to_JLFP in *.
                by rewrite TASK HP in LPjlp1.
                  by rewrite /jlfp_higher_eq_priority /FP_to_JLFP TASK.
          }
          have FLF2:
            forall t, 
              t1 <= t < t2 ->
              job_scheduled_at jlp1 t ->
              current_priority_ceiling jlp1 t = 0 ->
              False.
          { clear ARR SCHEDjlp1 NEQ t.
            intros t NEQ SCHED PR.
            move: (EX _ NEQ SCHED) => [jhp [NJ [ARR [BACK HP]]]].
            
            move: (H_respects_policy jhp jlp1 t ARR BACK SCHED) => PRIO.
            move: PRIO; rewrite /current_priority PR maxn0 geq_max; move => /andP [PRIO _].
            move: PRIO; rewrite leqNgt; move => /negP PRIO; apply: PRIO.
            apply leq_trans with (job_prio j).
            - unfold jlfp_lower_priority, FP_to_JLFP, lower_priority, higher_eq_priority in LPjlp1.
                by rewrite ltnNge.
            - by unfold jlfp_higher_eq_priority, FP_to_JLFP, higher_eq_priority in HP.
          }
          clear EX.
          unfold critical_sections_are_bounded in H_critical_sections_are_bounded.
          move: (H_critical_sections_are_bounded jlp1) => Bo.
          rewrite EQ in CONTR.
          unfold cumulative_priority_inversion in CONTR.
          move: (blocking_cannot_be_too_long
                   _ B H_B_positive (H_critical_sections_are_bounded jlp1) H_resource_locks_are_properly_nested
                   H_only_one_section_of_any_resource t1 t2 CONTR) => [tnc [NEQtnc [SCHED NICS]]].
            by eapply FLF2 with (t := tnc). 
        Qed.

      End PriorityInversionIsBounded.

      
      (** * TODO: smth *)
      (** TODO: comment *)
      (* TODO: name *)
      Section RTA.

        (* Let B a pos. const. and ... *)
        Variable B: time.
        Hypothesis H_B_positive: B > 0.
        Hypothesis H_critical_sections_are_bounded: forall j, critical_sections_are_bounded j B.

        
        Hypothesis H_resource_locks_are_properly_nested: critical_sections_are_properly_nested.

        Hypothesis H_proper_sections: critical_sections_are_properly_formed.

        Hypothesis H_only_one_section_of_any_resource: only_one_critical_section_of_any_resource.

        (* TODO: comment *) 
        Hypothesis H_respects_policy: respects_FP_policy_with_resources.

        
        (* Assume that max_arrivals is a "good" arrival curve,
         i.e. for all tsk in ts max_arrival tsk 0 is equal to 0 and 
         max_arrival is a monotone function for every tsk. *)
        Hypothesis H_max_arrival_zero: forall tsk, tsk \in ts -> max_arrivals tsk 0 = 0.
        Hypothesis H_max_arrival_monot: forall tsk, tsk \in ts -> monotone (max_arrivals tsk) leq.
        
        (* Let L be any positive fixed point of the busy interval recurrence. *)
        Variable L: time.
        Hypothesis H_L_positive: L > 0.
        Hypothesis H_fixed_point: L = B + total_hep_rbf L.

        (* Let's define the notion of search space for clarity. *)
        Let is_in_search_space A := (A < L) && (task_rbf A != task_rbf (A + ε)).

        (* Next, consider any value R, and assume that for any given arrival A from search space
           there is a solution of the response-time bound recurrence which is bounded by R. *)
        Variable R: nat.
        Hypothesis H_R_is_maximum: 
          forall A,
            is_in_search_space A -> 
            exists F,
              A + F = B + task_rbf (A + ε) + total_ohep_rbf (A + F) /\
              F <= R.

        (* TODO: comment *)
        (* TODO: name *)
        Lemma uniprocessor_response_time_bound:
          response_time_bounded_by tsk R.
        Proof.
          eapply fp_rta_theory.AbstractRTAforFPwithArrivalCurves.uniprocessor_response_time_bound_fp with
          (higher_eq_priority0 := higher_eq_priority)
            (max_arrivals0 := max_arrivals)
            (task_max := task_blocking)
            (task_last0 := task_last)
            (task_cost0 := task_cost)
            (job_max := job_blocking) 
            (job_last0 := job_last)
            (tsk0 := tsk)
            (ts0 := ts) 
            (L0 := L); eauto 2.
          - by intros x; unfold higher_eq_priority.
          - intros j t t' LE LI COMP.
            exfalso.
            rewrite /job_lock_in_service /job_last subnn subn0 in LI.
            move: COMP => /negP COMP; apply: COMP.
            rewrite /completed_by eqn_leq; apply/andP; split; first by done.
            apply leq_trans with (service sched j t); first by done.
              by apply  service_monotonic.
          - apply priority_inversion_is_bounded; eauto 2.
          - intros. 
            feed (H_R_is_maximum A).
            unfold is_in_search_space. 
            move: H => /andP [H1 H2].
            apply/andP; split; first by done.  
            apply/negP; intros CONTR; move: CONTR => /eqP CONTR.
            move: H2 => /negP H2; apply: H2.
            rewrite /task_rbf in CONTR. by rewrite CONTR.
            move: (H_R_is_maximum) => [F [H1 H2]].
            exists F; split.
            unfold ε, task_last. rewrite subnn subn0. by done.
            unfold ε, task_last. rewrite subnn addn0. by done.
        Qed.
        
      End RTA.

    End Analysis.
    
  End Locks.
     
End Locks.
