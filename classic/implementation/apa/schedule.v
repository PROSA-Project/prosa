Require Import prosa.classic.util.all.
Require Import prosa.classic.model.priority.
Require Import prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.arrival.basic.task.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.apa.affinity prosa.classic.model.schedule.apa.platform.
Require Import prosa.classic.model.schedule.global.transformation.construction.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import SporadicTaskset ArrivalSequence Schedule Platform Priority Affinity ScheduleConstruction.

  (* In this section, we implement a concrete weak APA scheduler. *)
  Section Implementation.
    
    Context {Job: eqType}.
    Context {sporadic_task: eqType}.

    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Let num_cpus denote the number of processors, ...*)
    Variable num_cpus: nat.

    (* ... and let arr_seq be any arrival sequence.*)
    Variable arr_seq: arrival_sequence Job.

    (* Let alpha be an affinity associated with each task. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    (* Assume a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy Job.

    (* Next, we show how to recursively construct the schedule. *)
    Section ScheduleConstruction.

      (* For any time t, suppose that we have generated the schedule prefix in the
         interval [0, t). Then, we must define what should be scheduled at time t. *)
      Variable sched_prefix: schedule Job num_cpus.
      Variable cpu: processor num_cpus.
      Variable t: time.

      (* For simplicity, let's use some local names. *)
      Let is_pending := pending job_arrival job_cost sched_prefix.
      Let actual_arrivals := jobs_arrived_up_to arr_seq.
      
      (* Consider the list of pending jobs at time t, ... *)
      Definition pending_jobs := [seq j <- actual_arrivals t | is_pending j t].

      (* ...which we sort by priority. *)
      Definition sorted_pending_jobs := sort (higher_eq_priority t) pending_jobs.

      (* Now we implement the algorithm that generates the APA schedule. *)

      (* Given a job j at time t, we first define a predicate that states
         whether j should preempt a mapping (cpu, x), where x is either Some j'
         that is currently mapped to cpu or None. *)
        Definition should_be_scheduled (j: Job) p :=
        let '(cpu, mapped_job) := p in
          if mapped_job is Some j' then (* If there is a job j', check the priority and affinity. *)
            (can_execute_on alpha (job_task j) cpu) &&
            ~~ (higher_eq_priority t j' j)
          else (* Else, if cpu is idle, check only the affinity. *)
            (can_execute_on alpha (job_task j) cpu).

      (* Next, using the "should_be_scheduled" predicate, we define a function
         that tries to schedule job j by updating a list of mappings.
         It does so by replacing the first pair (cpu, x) where j can be
         scheduled (if it exists). *)
      Definition update_available_cpu allocation j :=
        replace_first (should_be_scheduled j) (* search for processors that j can preempt *)
                      (set_pair_2nd (Some j)) (* replace the mapping in that processor with j *)
                      allocation. (* list of mappings *)

      (* Consider the empty mapping. *)
      Let empty_mapping : seq (processor num_cpus * option Job) :=
        (zip (enum (processor num_cpus)) (nseq num_cpus None)).
      
      (* Using the fuction "update_available_cpu", we now define an iteration
         that iteratively maps each pending job to a processor.

         Starting with an empty mapping,
         <(cpu0, None), (cpu1, None), (cpu2, None), ...>,
         it tries to schedule each job on some processor and yields an updated list: 
         <(cpu0, None), (cpu1, Some j5), (cpu2, Some j9), ...>. *)
      Definition schedule_jobs_from_list l :=
        foldl update_available_cpu empty_mapping l.

      (* To conclude, we take the list of pairs and convert to a function denoting
         the actual schedule. *)
      Definition apa_schedule :=
        pairs_to_function None (schedule_jobs_from_list sorted_pending_jobs) cpu.
      
    End ScheduleConstruction.

    (* Starting from the empty schedule, the final schedule is obtained by iteratively
       picking the highest-priority job. *)
    Let empty_schedule : schedule Job num_cpus := fun cpu t => None.
    Definition scheduler :=
      build_schedule_from_prefixes num_cpus apa_schedule empty_schedule.

    (* Then, by showing that the construction function depends only on the prefix, ... *)
    Lemma scheduler_depends_only_on_prefix:
      forall sched1 sched2 cpu t,
        (forall t0 cpu0, t0 < t -> sched1 cpu0 t0 = sched2 cpu0 t0) ->
        apa_schedule sched1 cpu t = apa_schedule sched2 cpu t.
    Proof.
      intros sched1 sched2 cpu t ALL.
      rewrite /apa_schedule /schedule_jobs_from_list; do 2 f_equal.
      rewrite /sorted_pending_jobs; f_equal.
      apply eq_in_filter.
      intros j ARR.
      rewrite /pending; do 2 f_equal.
      rewrite /completed; f_equal.
      apply eq_big_nat; move => i /= LTi.
      rewrite /service_at /scheduled_on; apply eq_bigl; move => cpu'.
      by rewrite ALL.
    Qed.
      
    (* ...we infer that the generated schedule is indeed based on the construction function. *)
    Corollary scheduler_uses_construction_function:
      forall t cpu, scheduler cpu t = apa_schedule scheduler cpu t.
    Proof.
      by ins; apply prefix_dependent_schedule_construction,
                    scheduler_depends_only_on_prefix.
    Qed.
    
  End Implementation.

  (* In this section, we prove several properties about the scheduling algorithm we
     implemented. For example, we show that it is APA work conserving. *)
  Section Proofs.

    Context {Job: eqType}.
    Context {sporadic_task: eqType}.

    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Assume a positive number of processors. *)
    Variable num_cpus: nat.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Let alpha be an affinity associated with each task. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    (* Let arr_seq be any job arrival sequence with consistent, duplicate-free arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Consider any JLDP policy higher_eq_priority that is transitive and total. *)
    Variable higher_eq_priority: JLDP_policy Job.
    Hypothesis H_priority_transitive: JLDP_is_transitive higher_eq_priority.
    Hypothesis H_priority_total: forall t, total (higher_eq_priority t).
    
    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_arrival job_cost job_task num_cpus arr_seq alpha higher_eq_priority.
    
    (* Next, we provide some helper lemmas about the scheduler construction. *)
    Section HelperLemmas.

      (* To avoid many parameters, let's also rename the scheduling function.
         We make a generic version (for any list of jobs l), ... *)
      Let schedule_jobs t l := schedule_jobs_from_list job_task num_cpus alpha higher_eq_priority t l.
      (* ... and a specific version (for the pending jobs in sched). *)
      Let schedule_pending_jobs t :=
        schedule_jobs t (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq
                                             higher_eq_priority sched t).

      (* Next, we show that there are no duplicate cpus in the mapping. *)
      Lemma scheduler_uniq_cpus :
        forall t l,
          uniq (unzip1 (schedule_jobs t l)).
      Proof.
        intros t l.
        induction l as [| l' j_last] using last_ind.
        {
          by rewrite unzip1_zip; [rewrite enum_uniq | rewrite size_enum_ord size_nseq].
        }
        {
          rewrite /schedule_jobs /schedule_jobs_from_list -cats1 foldl_cat /=.
          set up := update_available_cpu _ _ _ _ _.
          assert (EQ: forall l j, unzip1 (up l j) = unzip1 l). 
          {
            intros l j; clear -l j.
            induction l; first by done.
            rewrite /up /update_available_cpu /=.
            by case SHOULD: should_be_scheduled; simpl; f_equal.
          }
          by rewrite EQ.
        }
      Qed.

      (* Next, we show that if a job j is in the mapping, then j must come from the list
         of jobs l used in the construction. *)
      Lemma scheduler_job_in_mapping :
        forall l j t cpu,
          (cpu, Some j) \in schedule_jobs t l -> j \in l.
      Proof.
        intros l j t cpu SOME; clear -SOME.
        induction l as [| l' j'] using last_ind; simpl in *.
        {
          apply mem_zip in SOME; last by rewrite size_enum_ord size_nseq.
          by move: SOME => [_ /nseqP [SOME _]].
        }
        {
          rewrite /schedule_jobs /schedule_jobs_from_list -cats1 foldl_cat /= in SOME.
          unfold update_available_cpu in SOME.
          elim (replace_first_cases SOME) => [IN | [y [NEW IN]]].
          {
            by rewrite mem_rcons in_cons; apply/orP; right; apply IHl.
          }
          {
            case: NEW => EQ1 EQ2; subst.
            by rewrite mem_rcons in_cons eq_refl orTb.
          }
        }
      Qed.

      (* Next, we prove that if a pair (cpu, j) is in the mapping, then
         cpu must be part of j's affinity. *)
      Lemma scheduler_mapping_respects_affinity :
        forall j t cpu,
          (cpu, Some j) \in schedule_pending_jobs t ->
          can_execute_on alpha (job_task j) cpu.
      Proof.
        intros j t cpu SOME.
        unfold schedule_pending_jobs in SOME.
        set l := sorted_pending_jobs _ _ _ _ _ _ _ in SOME.
        induction l as [| l' j'] using last_ind; simpl in *.
        {
          apply mem_zip in SOME; last by rewrite size_enum_ord size_nseq.
          by move: SOME => [_ /nseqP [BUG _]].
        }
        {
          unfold schedule_jobs, schedule_jobs_from_list in SOME.
          rewrite -cats1 foldl_cat /= in SOME.
          elim (replace_first_cases SOME) => [IN | [y [NEW [SHOULD _]]]];
            first by apply IHl.
          case: NEW => EQ1 EQ2; subst.
          by unfold should_be_scheduled in SHOULD; desf.
        }
      Qed.

      (* Next, we show that the mapping does not schedule the same job j in two
         different cpus. *)
      Lemma scheduler_has_no_duplicate_jobs :
        forall j t cpu1 cpu2,
          (cpu1, Some j) \in schedule_pending_jobs t ->
          (cpu2, Some j) \in schedule_pending_jobs t ->
          cpu1 = cpu2.
      Proof.
        intros j t cpu1 cpu2 SOME1 SOME2.
        unfold schedule_pending_jobs in *.
        set l := sorted_pending_jobs _ _ _ _ _ _ _ in SOME1 SOME2.
        assert (UNIQ: uniq l).
          by rewrite sort_uniq; eapply filter_uniq, arrivals_uniq; eauto 1.
          
        induction l as [| l' j'] using last_ind; simpl in *.
        {
          apply mem_zip in SOME1; last by rewrite size_enum_ord size_nseq.
          by move: SOME1 => [_ /nseqP [BUG _]].
        }
        {
          rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
          rewrite /schedule_jobs /schedule_jobs_from_list -cats1 foldl_cat /= in SOME1 SOME2.
          destruct (replace_first_cases SOME1) as [SAME1 | [[cpu1' p1] [EQ1 [SHOULD1 PREV1]]]];
          destruct (replace_first_cases SOME2) as [SAME2 | [[cpu2' p2] [EQ2 [SHOULD2 PREV2]]]].
          {
            by apply IHl.
          }
          {
            move: EQ2; case => EQ1 EQ2; subst cpu2' j'.
            destruct p2 as [j2 |].
            {
              apply scheduler_job_in_mapping in SAME1.
              by rewrite SAME1 in NOTIN.
            }
            by apply (replace_first_new _ _ _ (cpu2, Some j)) in SOME1;
              [by move: SOME1; case => -> | | | by done];
              apply/negP; intro BUG;
              apply scheduler_job_in_mapping in BUG;
              by rewrite BUG in NOTIN.
          }
          {
            move: EQ1; case => EQ1 EQ2; subst cpu1' j'.
            destruct p1 as [j1 |].
            {
              apply scheduler_job_in_mapping in SAME2.
              by rewrite SAME2 in NOTIN.
            }
            by apply (replace_first_new _ _ _ (cpu2, Some j)) in SOME1;
              [by move: SOME1; case => -> | | | by done];
              apply/negP; intro BUG;
              apply scheduler_job_in_mapping in BUG;
              by rewrite BUG in NOTIN.
          }
          {
            move: EQ1; case => /= EQ1' /= EQ2'; subst cpu1' j'.
            move: EQ2; case => EQ1'; subst cpu2'.
            by apply (replace_first_new _ _ _ (cpu2, Some j)) in SOME1;
              [by move: SOME1; case => -> | | | by done];
              apply/negP; intro BUG;
              apply scheduler_job_in_mapping in BUG;
              by rewrite BUG in NOTIN.
          }
        }
      Qed.

      (* Based on the definition of the schedule, a job j is scheduled on cpu
         iff (cpu, Some j) is the final mapping. *)
      Lemma scheduler_scheduled_on :
        forall j cpu t,
          scheduled_on sched j cpu t = ((cpu, Some j) \in schedule_pending_jobs t).
      Proof.
        unfold schedule_pending_jobs, schedule_jobs in *.
        intros j cpu t.
        apply/idP/idP.
        {
          move => /eqP SCHED.
          rewrite /sched scheduler_uses_construction_function /apa_schedule in SCHED.
          by apply pairs_to_function_neq_default in SCHED; last by done.
        }
        {
          intros SCHED.
          have MEM := pairs_to_function_mem None.
          apply MEM in SCHED; clear MEM; last by apply scheduler_uniq_cpus.
          apply/eqP.
          by rewrite /sched scheduler_uses_construction_function.
        }
      Qed.

      (* Now we show that for every cpu, there is always a pair in the mapping. *)
      Lemma scheduler_has_cpus :
        forall cpu t l,
          exists x,
            (cpu, x) \in schedule_jobs t l. 
      Proof.
        intros cpu t l.
        induction l as [| l' j_last] using last_ind; simpl in *.
        {
          by exists None; rewrite mem_zip_nseq_r;
            [by rewrite mem_enum | by rewrite size_enum_ord].
        }
        {
          rewrite /schedule_jobs /schedule_jobs_from_list -cats1 foldl_cat /=.
          move: IHl => [x IN].
          eapply replace_first_previous in IN; des;
            first by exists x; apply IN.
          rewrite /set_pair_2nd in IN.
          by exists (Some j_last); apply IN0.
        }
      Qed.

      (* Next, consider a list of jobs l that is sorted by priority and does not have
         duplicates.
         We prove that for any job j in l, if j is not scheduled at time t,
         then every cpu in j's affinity has some job mapped at time t.  *)
      Lemma scheduler_mapping_is_work_conserving :
        forall j cpu t l,
          j \in l ->
          sorted (higher_eq_priority t) l ->
          uniq l ->
          (forall cpu, (cpu, Some j) \notin schedule_jobs t l) ->
          can_execute_on alpha (job_task j) cpu ->
          exists j_other,
            (cpu, Some j_other) \in schedule_jobs t l.
      Proof.
        intros j cpu t l IN SORT UNIQ NOTSCHED CAN.        
        generalize dependent cpu.
        induction l as [| l' j_last] using last_ind; simpl in *;
          first by rewrite in_nil in IN.
        {
          intros cpu CAN.
          rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
          rewrite /schedule_jobs /schedule_jobs_from_list -cats1 foldl_cat /= in NOTSCHED *.
          set prev := foldl _ _ _ in NOTSCHED *.
          rewrite mem_rcons in_cons in IN.
          move: IN => /orP [/eqP IN | LAST]; subst.
          {
            clear IHl.
            assert (ALL: forall x, x \in prev ->
                  ~~ (should_be_scheduled job_task num_cpus alpha higher_eq_priority t j_last) x).
            {
              apply replace_first_failed with (f := set_pair_2nd (Some j_last)).
              by intros [cpu' j'] IN; apply NOTSCHED.
            }
            have [x IN] := scheduler_has_cpus cpu t l'; fold prev in IN.
            specialize (ALL (cpu, x) IN).
            simpl in ALL.
            destruct x as [j' |]; last by rewrite CAN in ALL.
            eapply replace_first_previous in IN; des; first by exists j'; apply IN.
            by exists j_last; apply IN0.              
          }
          {
            specialize (IHl LAST).
            feed_n 2 IHl;
              [by apply sorted_rcons_prefix in SORT | by done | ].
            feed IHl.
            {
              clear IHl; intros cpu'; specialize (NOTSCHED cpu').
              apply/negP; intro BUG.
              apply replace_first_previous with (f := set_pair_2nd (Some j_last))
                (P := should_be_scheduled job_task num_cpus alpha higher_eq_priority t j_last)
                in BUG; des;
                first by rewrite BUG in NOTSCHED.
              move: BUG => /andP [_ /negP HP].
              by apply HP, order_sorted_rcons with (xs := l'); try by done.
            }
            move: (IHl cpu CAN) => [j_old IN]; clear IHl LAST.
            by eapply replace_first_previous in IN; des;
              [exists j_old; apply IN | exists j_last; apply IN0].
          }
        }
      Qed.

      (* Next, we prove that the mapping respects priority. *)
      Lemma scheduler_priority :
        forall j j_hp cpu t,
          arrives_in arr_seq j ->
          backlogged job_arrival job_cost sched j t ->
          can_execute_on alpha (job_task j) cpu ->
          scheduled_on sched j_hp cpu t ->
          higher_eq_priority t j_hp j.
      Proof.
        have SCHED_ON := scheduler_scheduled_on.
        intros j j_hp cpu t ARRj BACK CAN SCHED.
        move: BACK => /andP [PENDING NOTSCHED'].
        assert (NOTSCHED: forall cpu, (cpu, Some j) \notin schedule_pending_jobs t). 
        {
          intros cpu'; rewrite -SCHED_ON.
          by rewrite negb_exists in NOTSCHED'; move: NOTSCHED' => /forallP ALL; apply ALL.
        }
        rewrite SCHED_ON in SCHED.
        clear NOTSCHED' SCHED_ON.

        unfold schedule_pending_jobs, schedule_jobs, schedule_jobs_from_list in *.
        set l := sorted_pending_jobs _ _ _ _ _ _ _ in SCHED NOTSCHED.
        
        have IN: j \in l.
        {
          rewrite mem_sort mem_filter PENDING andTb.
          move: PENDING => /andP [ARR IN]; rewrite /has_arrived in ARR.
          by apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival).
        }
        have INhp: j_hp \in l by apply scheduler_job_in_mapping in SCHED.
        have SORT : sorted (higher_eq_priority t) l by apply sort_sorted, H_priority_total. 
        have UNIQ: uniq l.
          by rewrite sort_uniq filter_uniq // (arrivals_uniq job_arrival) //.

        induction l as [| l' j_last] using last_ind;
          first by rewrite in_nil in IN.
        {
          rewrite /schedule_jobs_from_list -cats1 foldl_cat /= in SCHED.
          rewrite /schedule_jobs_from_list -cats1 foldl_cat /= in NOTSCHED.
          set prev := foldl _ _ _ in SCHED NOTSCHED.
          rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
          rewrite 2!mem_rcons 2!in_cons in IN INhp.
          move: IN => /orP [/eqP EQ | IN];
          move: INhp => /orP [/eqP EQhp | INhp].
          {
            subst j_last j_hp.
            by specialize (NOTSCHED cpu); rewrite SCHED in NOTSCHED.
          }
          {
            subst j_last.
            by apply order_sorted_rcons with (xs := l').
          }
          {
            subst j_last; clear IHl.
            destruct (replace_first_cases SCHED) as [PREV | [[cpu' y] [EQ [SHOULD IN']]]].
            {
              unfold prev in PREV.
              apply scheduler_job_in_mapping in PREV.
              by rewrite PREV in NOTIN.
            }
            {
              move: EQ; case; intro EQ1; subst cpu'.
              destruct y as [j'|].
              {
                unfold should_be_scheduled in SHOULD.
                move: SHOULD => /andP [CAN' /negP HP].
                unfold prev in IN'.
                apply scheduler_job_in_mapping in IN'.
                by exfalso; apply HP, order_sorted_rcons with (xs := l').
              }
              {
                destruct [exists cpu, ((cpu, Some j) \in prev)] eqn:EX.
                {
                  move: EX => /existsP [cpu' IN''].
                  unfold prev in IN''.
                  apply replace_first_previous with (f := set_pair_2nd (Some j_hp))
                    (P := should_be_scheduled job_task num_cpus alpha higher_eq_priority t j_hp)
                      in IN''; des;
                    first by specialize (NOTSCHED cpu'); rewrite IN'' in NOTSCHED.
                  move: IN'' => /andP [_ /negP HP].
                  by exfalso; apply HP, order_sorted_rcons with (xs := l').
                }
                {
                  apply negbT in EX; rewrite negb_exists in EX.
                  move: EX => /forallP EX.
                  apply sorted_rcons_prefix in SORT.
                  move: (scheduler_mapping_is_work_conserving j cpu t l' IN SORT UNIQ EX CAN) => [j' BUG].
                  have MEM := pairs_to_function_mem None.
                  apply MEM in BUG; last by apply scheduler_uniq_cpus.
                  have UNIQ' := scheduler_uniq_cpus t l'.
                  apply MEM in IN'; last by apply UNIQ'.
                  by rewrite IN' in BUG.
                }
              }
            }
          }
          {
            apply IHl; try (by done); last first.
            {
              by apply sorted_rcons_prefix in SORT.
            }
            {
              intros cpu0; apply/negP; intro BUG.
              unfold update_available_cpu in NOTSCHED.
              apply replace_first_previous with (f := set_pair_2nd (Some j_last))
                (P := should_be_scheduled job_task num_cpus alpha higher_eq_priority t j_last)
                  in BUG; des.
              {
                by specialize (NOTSCHED cpu0); rewrite BUG in NOTSCHED.
              }
              {
                move: BUG => /andP [_ /negP HP].
                by apply HP, order_sorted_rcons with (xs := l'); try by done.
              }
            }
            {
              destruct (replace_first_cases SCHED) as [| [[cpu' y][EQ [SHOULD IN']]]]; first by done.
              move: EQ; case; intros EQ1 EQ2; subst cpu' j_last.
              by rewrite INhp in NOTIN.
            }
          }
        }
      Qed.

    End HelperLemmas.

    (* Now, we prove the important properties about the implementation. *)
    
    (* First, we show that scheduled jobs come from the arrival sequence. *)
    Lemma scheduler_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    Proof.
      move => j t /existsP [cpu SCHED].
      rewrite scheduler_scheduled_on in SCHED.
      apply scheduler_job_in_mapping in SCHED.
      rewrite mem_sort mem_filter in SCHED.
      move: SCHED => /andP [_ ARR].
      by apply in_arrivals_implies_arrived in ARR.
    Qed.
      
    (* Jobs do not execute before they arrive, ...*)
    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Proof.
      move => j t /existsP [cpu SCHED].
      rewrite scheduler_scheduled_on in SCHED.
      apply scheduler_job_in_mapping in SCHED.
      rewrite mem_sort mem_filter in SCHED.
      by move: SCHED => /andP [/andP [ARR _] _].
    Qed.

    (* ..., jobs are sequential, ... *)
    Theorem scheduler_sequential_jobs: sequential_jobs sched.
    Proof.
      intros j t cpu1 cpu2 SCHED1 SCHED2.
      by apply scheduler_has_no_duplicate_jobs with (j := j) (t := t);
      rewrite -scheduler_scheduled_on; apply/eqP.
    Qed.
               
    (* ... and jobs do not execute after completion. *)
    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      have SEQ := scheduler_sequential_jobs.
      intros j t.
      induction t;
        first by rewrite /service /service_during big_geq //.
      rewrite /service /service_during big_nat_recr //=.
      rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LT]; last first.
      {
        apply: leq_trans LT; rewrite -addn1.
        apply leq_add; first by done.
        rewrite /service_at.
        case (boolP ([exists cpu, scheduled_on sched j cpu t])) => [EX | ALL]; last first.
        {
          rewrite negb_exists in ALL; move: ALL => /forallP ALL.
          rewrite big1 //; intros cpu SCHED.
          by specialize (ALL cpu); rewrite SCHED in ALL.
        }
        move: EX => /existsP [cpu SCHED].
        rewrite (bigD1 cpu) /=; last by done.
        rewrite big1; first by rewrite addn0.
        move => cpu' /andP [SCHED' NEQ].
        move: SCHED SCHED' => /eqP SCHED /eqP SCHED'.
        move: NEQ => /eqP NEQ; exfalso; apply: NEQ.
        by apply SEQ with (j := j) (t := t).
      }
      rewrite -[job_cost _]addn0; apply leq_add; first by rewrite -EQ.
      rewrite leqn0 /service_at big1 //.
      move => cpu SCHED.
      rewrite scheduler_scheduled_on in SCHED.
      apply scheduler_job_in_mapping in SCHED.
      rewrite mem_sort mem_filter in SCHED.
      move: SCHED => /andP [/andP [_ NOTCOMP] _].
      by rewrite /completed EQ leqnn in NOTCOMP.
    Qed.

    (* In addition, the scheduler is APA work conserving, ... *)
    Theorem scheduler_apa_work_conserving:
      apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha.
    Proof.
      intros j t ARRj BACK cpu CAN.
      set l := (sorted_pending_jobs job_arrival job_cost num_cpus arr_seq higher_eq_priority sched t).
      have SORT : sorted (higher_eq_priority t) l by apply sort_sorted, H_priority_total. 
      have UNIQ: uniq l.
        by rewrite sort_uniq filter_uniq // (arrivals_uniq job_arrival) //.
      move: BACK => /andP [PENDING NOTSCHED].
      have IN: j \in l.
      {
        rewrite mem_sort mem_filter PENDING andTb.
        move: PENDING => /andP [ARR _].
        by apply arrived_between_implies_in_arrivals with (job_arrival0 := job_arrival).
      }
      have WORK := scheduler_mapping_is_work_conserving j cpu t l IN SORT UNIQ.
      exploit WORK; try by done.
      {
        rewrite negb_exists in NOTSCHED; move: NOTSCHED => /forallP NOTSCHED.
        by intros cpu0; specialize (NOTSCHED cpu0); rewrite -scheduler_scheduled_on.
      }
      by move => [j_other IN']; exists j_other; rewrite scheduler_scheduled_on.
    Qed.  

    (* ..., respects affinities, ... *)
    Theorem scheduler_respects_affinity:
      respects_affinity job_task sched alpha.
    Proof.
      unfold respects_affinity; intros j cpu t SCHED.
      apply scheduler_mapping_respects_affinity with (t := t).
      by rewrite -scheduler_scheduled_on.
    Qed.
    
    (* ... and respects the JLDP policy under weak APA scheduling. *)
    Theorem scheduler_respects_policy :
      respects_JLDP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
                                          sched alpha higher_eq_priority.
    Proof.
      unfold respects_JLDP_policy_under_weak_APA.
      intros j j_hp cpu t ARRj BACK SCHED ALPHA.
      rewrite scheduler_scheduled_on in SCHED.
      apply scheduler_priority with (cpu := cpu); try by done.
      by rewrite scheduler_scheduled_on.
    Qed.

  End Proofs.
    
End ConcreteScheduler.