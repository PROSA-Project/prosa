Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.global.response_time rt.model.schedule.global.workload
               rt.model.schedule.global.schedulability.
Require Import rt.model.schedule.global.basic.schedule rt.model.schedule.global.basic.platform
               rt.model.schedule.global.basic.interference rt.model.schedule.global.basic.interference_edf.
Require Import rt.analysis.global.parallel.workload_bound
               rt.analysis.global.parallel.interference_bound.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module InterferenceBoundEDF.

  Import Job SporadicTaskset Schedule ScheduleOfSporadicTask Schedulability
         WorkloadBound ResponseTime Priority
         TaskArrival Interference InterferenceEDF.
  Export InterferenceBoundGeneric.

  (* In this section, we define Bertogna and Cirinei's EDF-specific
     interference bound. *)
  Section SpecificBoundDef.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    (* Consider the interference incurred by tsk in a window of length delta... *)
    Variable delta: time.

    (* due to a different task tsk_other, with response-time bound R_other. *)
    Variable tsk_other: sporadic_task.
    Variable R_other: time.

    (* Bertogna and Cirinei define the following bound for task interference
       under EDF scheduling. *)
    Definition edf_specific_interference_bound :=
      let d_tsk := task_deadline tsk in
      let e_other := task_cost tsk_other in
      let p_other := task_period tsk_other in
      let d_other := task_deadline tsk_other in
        (div_ceil (d_tsk + R_other - d_other + 1) p_other) * e_other.

  End SpecificBoundDef.
  
  (* Next, we define the total interference bound for EDF, which combines the generic
     and the EDF-specific bounds. *)
  Section TotalInterferenceBoundEDF.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section RecallInterferenceBounds.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.

      (* By combining Bertogna's interference bound for a work-conserving
         scheduler ... *)
      Let basic_interference_bound := interference_bound_generic task_cost task_period delta tsk_R.

      (* ... with and EDF-specific interference bound, ... *)
      Let edf_specific_bound := edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other.

      (* Bertogna and Cirinei define the following interference bound
         under EDF scheduling. *)
      Definition interference_bound_edf :=
        minn basic_interference_bound edf_specific_bound.

    End RecallInterferenceBounds.

    (* Next we define the computation of the total interference for APA scheduling. *)
    Section TotalInterference.

      (* Let other_task denote tasks different from tsk. *)
      Let other_task := different_task tsk.
      
      (* The total interference incurred by tsk is bounded by the sum
         of individual task interferences of the other tasks. *)
      Definition total_interference_bound_edf :=
        \sum_((tsk_other, R_other) <- R_prev | other_task tsk_other)
           interference_bound_edf (tsk_other, R_other).

    End TotalInterference.

  End TotalInterferenceBoundEDF.
  
  (* In this section, we show that the EDF-specific interference bound is safe. *)
  Section ProofSpecificBound.

    Import Schedule Interference Platform SporadicTaskset.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Assume there exists at least one processor. *)
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Assume that we have a task set where all tasks have valid
       parameters and constrained deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.

    (* Assume that the scheduler is a work-conserving EDF scheduler. *)
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_edf_scheduler:
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline).

    (* Let tsk_i be the task to be analyzed, ...*)
    Variable tsk_i: sporadic_task.
    Hypothesis H_tsk_i_in_task_set: tsk_i \in ts.
    
    (* and j_i one of its jobs. *)
    Variable j_i: Job.
    Hypothesis H_j_i_arrives: arrives_in arr_seq j_i.
    Hypothesis H_job_of_tsk_i: job_task j_i = tsk_i.

    (* Let tsk_k denote any interfering task, ... *)
    Variable tsk_k: sporadic_task.
    Hypothesis H_tsk_k_in_task_set: tsk_k \in ts.

    (* ...and R_k its response-time bound. *)
    Variable R_k: time.
    Hypothesis H_R_k_le_deadline: R_k <= task_deadline tsk_k.
    
    (* Consider a time window of length delta <= D_i, starting with j_i's arrival time. *)
    Variable delta: time.
    Hypothesis H_delta_le_deadline: delta <= task_deadline tsk_i.

    (* Assume that the jobs of tsk_k satisfy the response-time bound before the end of the interval *)
    Hypothesis H_all_previous_jobs_completed_on_time :
      forall j_k,
        arrives_in arr_seq j_k ->
        job_task j_k = tsk_k ->
        job_arrival j_k + R_k < job_arrival j_i + delta ->
        completed job_cost sched j_k (job_arrival j_k + R_k).

    (* In this section, we prove that Bertogna and Cirinei's EDF interference bound
       indeed bounds the interference caused by task tsk_k in the interval [t1, t1 + delta). *)
    Section MainProof.
                                    
      (* Let's call x the task interference incurred by job j due to tsk_k. *)
      Let x :=
        task_interference job_arrival job_cost job_task sched j_i
                          tsk_k (job_arrival j_i) (job_arrival j_i + delta).

      (* Also, recall the EDF-specific interference bound for EDF. *)
      Let interference_bound :=
        edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k.

      (* Let's simplify the names a bit. *)
      Let t1 := job_arrival j_i.
      Let t2 := job_arrival j_i + delta.
      Let D_i := task_deadline tsk_i.
      Let D_k := task_deadline tsk_k.
      Let p_k := task_period tsk_k.

      Let n_k := div_ceil (D_i + R_k - D_k + 1) p_k.

      (* Let's give a simpler name to job interference. *)
      Let interference_caused_by := job_interference job_arrival job_cost sched j_i.
      
      (* Identify the subset of jobs that actually cause interference *)
      Let interfering_jobs :=
        filter (fun j' =>
                 (job_task j' == tsk_k) && (interference_caused_by j' t1 t2 != 0))
               (jobs_scheduled_between sched t1 t2).
      
      (* Now, consider the list of interfering jobs sorted by arrival time. *)
      Let earlier_arrival := fun x y => job_arrival x <= job_arrival y.
      Let sorted_jobs := sort earlier_arrival interfering_jobs.

      (* Now we proceed with the proof.
         The first step consists in simplifying the sum corresponding to the workload. *)
      Section SimplifyJobSequence.

        (* Use the alternative definition of task interference, based on
           individual job interference. *)
        Lemma interference_bound_edf_use_another_definition :
          x <= \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_k)
                interference_caused_by j t1 t2.
        Proof.
          unfold x, task_interference, interference_caused_by, job_interference.
          rewrite [\sum_(_ <- _ sched _ _ | _) _]exchange_big /=.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
          apply leq_sum. move => t /andP [LEt _].
          rewrite exchange_big /=.
          apply leq_sum; intros cpu _.
          destruct (backlogged job_arrival job_cost sched j_i t) eqn:BACK;
            last by rewrite andFb (eq_bigr (fun x => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0.
          rewrite andTb.
          destruct (task_scheduled_on job_task sched tsk_k cpu t) eqn:SCHED;
            last by done.
          unfold task_scheduled_on in *.
          destruct (sched cpu t) eqn:SOME; last by done.
          rewrite big_mkcond /= (bigD1_seq s) /=; last by apply undup_uniq.
          {
            rewrite SCHED -addn1 addnC; apply leq_add; last by done.
            apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
            by unfold scheduled_on; apply/eqP.
          }
          {
            unfold jobs_scheduled_between.
            rewrite mem_undup; apply mem_bigcat_nat with (j := t);
              first by done.
            apply mem_bigcat_ord with (j := cpu); first by apply ltn_ord.
            by unfold make_sequence; rewrite SOME mem_seq1 eq_refl.
          }
        Qed.

        (* Remove the elements that we don't care about from the sum *)
        Lemma interference_bound_edf_simpl_by_filtering_interfering_jobs :
          \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_k)
             interference_caused_by j t1 t2 = 
          \sum_(j <- interfering_jobs) interference_caused_by j t1 t2.
        Proof.
          unfold interfering_jobs; rewrite big_filter.
          rewrite big_mkcond; rewrite [\sum_(_ <- _ | _) _]big_mkcond /=.
          apply eq_bigr; intros i _; clear -i.
          destruct (job_task i == tsk_k); rewrite ?andTb ?andFb; last by done.
          destruct (interference_caused_by i t1 t2 != 0) eqn:DIFF; first by done.
          by apply negbT in DIFF; rewrite negbK in DIFF; apply/eqP.
        Qed.

        (* Then, we consider the sum over the sorted sequence of jobs. *)
        Lemma interference_bound_edf_simpl_by_sorting_interfering_jobs :
          \sum_(j <- interfering_jobs) interference_caused_by j t1 t2 =
           \sum_(j <- sorted_jobs) interference_caused_by j t1 t2.
        Proof.
          by rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Note that both sequences have the same set of elements. *)
        Lemma interference_bound_edf_job_in_same_sequence :
          forall j,
            (j \in interfering_jobs) = (j \in sorted_jobs).
        Proof.
          by apply perm_eq_mem; rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Also recall that all jobs in the sorted sequence is an interfering job of tsk_k, ... *)
        Lemma interference_bound_edf_all_jobs_from_tsk_k :
          forall j,
            j \in sorted_jobs ->
            arrives_in arr_seq j /\
            job_task j = tsk_k /\
            interference_caused_by j t1 t2 != 0 /\
            j \in jobs_scheduled_between sched t1 t2.
        Proof.
          intros j LT.
          rewrite -interference_bound_edf_job_in_same_sequence mem_filter in LT.
          move: LT => /andP [/andP [/eqP JOBi SERVi] INi].
          repeat split; try (by done).
          unfold jobs_scheduled_between in *; rewrite mem_undup in INi.
          apply mem_bigcat_nat_exists in INi; des.
          rewrite mem_scheduled_jobs_eq_scheduled in INi.
          by apply (H_jobs_come_from_arrival_sequence j i). 
        Qed.

        (* ...and consecutive jobs are ordered by arrival. *)
        Lemma interference_bound_edf_jobs_ordered_by_arrival :
          forall i elem,
            i < (size sorted_jobs).-1 ->
            earlier_arrival (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1).
        Proof.
          intros i elem LT.
          assert (SORT: sorted earlier_arrival sorted_jobs).
            by apply sort_sorted; unfold total, earlier_arrival; ins; apply leq_total.
          by destruct sorted_jobs; simpl in *; [by rewrite ltn0 in LT | by apply/pathP].
        Qed.

        (* Also, for any job of task tsk_k, the interference is bounded by the task cost. *)
        Lemma interference_bound_edf_interference_le_task_cost :
          forall j,
            j \in interfering_jobs ->
            interference_caused_by j t1 t2 <= task_cost tsk_k.
        Proof.
          rename H_valid_job_parameters into PARAMS.
          intros j INj.
          feed (interference_bound_edf_all_jobs_from_tsk_k j);
            first by rewrite -interference_bound_edf_job_in_same_sequence.
          move => [ARRj [TSKj _]].
          specialize (PARAMS j ARRj); des.
          apply leq_trans with (n := service_during sched j t1 t2);
            first by apply job_interference_le_service.
          by apply cumulative_service_le_task_cost with (job_task0 := job_task)
            (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline).
        Qed.

      End SimplifyJobSequence.

      (* Next, we show that if the number of jobs is no larger than n_k,
         the workload bound trivially holds. *)
      Section InterferenceFewJobs.

        Hypothesis H_few_jobs: size sorted_jobs <= n_k.
        
        Lemma interference_bound_edf_holds_for_at_most_n_k_jobs :
           \sum_(j <- sorted_jobs) interference_caused_by j t1 t2 <=
             interference_bound.
        Proof.
          unfold interference_bound, edf_specific_interference_bound; fold D_i p_k n_k.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk_k);
            last first.
          {
            rewrite big_const_seq iter_addn addn0 count_predT mulnC.
            by rewrite leq_mul2r; apply/orP; right.
          }
          {
            rewrite big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
            apply leq_sum; move => j /andP [IN _].
            apply interference_bound_edf_interference_le_task_cost.
            by rewrite interference_bound_edf_job_in_same_sequence. 
          }
        Qed.

      End InterferenceFewJobs.

      (* Otherwise, assume that the number of jobs is larger than n_k >= 0. *)
      Section InterferenceManyJobs.

        Hypothesis H_many_jobs: n_k < size sorted_jobs.

        (* This trivially implies that there's at least one job. *)
        Lemma interference_bound_edf_at_least_one_job: size sorted_jobs > 0.
        Proof.
          by apply leq_ltn_trans with (n := n_k).
        Qed.

        (* Let j_fst be the first job, and a_fst its arrival time. *)
        Variable elem: Job.
        Let j_fst := nth elem sorted_jobs 0.
        Let a_fst := job_arrival j_fst.

        (* In this section, we prove some basic lemmas about j_fst. *)
        Section FactsAboutFirstJob.
          
          (* The first job is an interfering job of task tsk_k. *)
          Lemma interference_bound_edf_j_fst_is_job_of_tsk_k :
            arrives_in arr_seq j_fst /\
            job_task j_fst = tsk_k /\
            interference_caused_by j_fst t1 t2 != 0 /\
            j_fst \in jobs_scheduled_between sched t1 t2.
          Proof.
            by apply interference_bound_edf_all_jobs_from_tsk_k, mem_nth,
                     interference_bound_edf_at_least_one_job.
          Qed.

          (* The deadline of j_fst is the deadline of tsk_k. *)
          Lemma interference_bound_edf_j_fst_deadline :
            job_deadline j_fst = task_deadline tsk_k.
          Proof.
            unfold valid_sporadic_job in *.
            rename H_valid_job_parameters into PARAMS.
            have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
            destruct FST as [FSTarr [FSTtask _]].
            by specialize (PARAMS j_fst FSTarr); des; rewrite PARAMS1 FSTtask.
          Qed.

          (* The deadline of j_i is the deadline of tsk_i. *)
          Lemma interference_bound_edf_j_i_deadline :
            job_deadline j_i = task_deadline tsk_i.
          Proof.
            unfold valid_sporadic_job in *.
            rename H_valid_job_parameters into PARAMS,
                   H_job_of_tsk_i into JOBtsk.
            by specialize (PARAMS j_i H_j_i_arrives); des; rewrite PARAMS1 JOBtsk.
          Qed.

          (* If j_fst completes by its response-time bound, then t1 <= a_fst + R_k,
             where t1 is the beginning of the time window (arrival of j_i). *)
          Lemma interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval :
            completed job_cost sched j_fst (a_fst + R_k) ->
            t1 <= a_fst + R_k.
          Proof.
            intros RBOUND.
            rewrite leqNgt; apply/negP; unfold not; intro BUG.
            have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
            destruct FST as [_ [_ [ FSTserv _]]].
            move: FSTserv => /negP FSTserv; apply FSTserv.
            rewrite -leqn0; apply leq_trans with (n := service_during sched j_fst t1 t2);
              first by apply job_interference_le_service.
            rewrite leqn0; apply/eqP.
            by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost)
                                              (job_arrival0 := job_arrival) (R := R_k);
              try (by done); apply ltnW.
          Qed. 
          
        End FactsAboutFirstJob.
        
        (* Now, let's prove the interference bound for the particular case of a single job.
           This case must be solved separately because the single job can simultaneously
           be carry-in and carry-out job, so its response time is not necessarily
           bounded by R_k (from the hypothesis H_all_previous_jobs_completed_on_time). *)
        Section InterferenceSingleJob.

          (* Assume that there's at least one job in the sorted list. *)
          Hypothesis H_only_one_job: size sorted_jobs = 1.
          
          Lemma interference_bound_edf_holds_for_a_single_job :
            interference_caused_by j_fst t1 t2 <= interference_bound.
          Proof.
            unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
            rename H_many_jobs into NUM,
                   H_valid_task_parameters into PARAMS,
                   H_only_one_job into SIZE.
            apply leq_trans with (n := task_cost tsk_k).
            {
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite SIZE.
            }
            {
              unfold interference_bound, edf_specific_interference_bound.
              rewrite -{1}[task_cost tsk_k]mul1n.
              rewrite leq_mul2r; apply/orP; right.
              exploit (PARAMS tsk_i); [by done | intro PARAMSi]; des.
              exploit (PARAMS tsk_k); [by done | intro PARAMSk]; des.
              apply ceil_neq0; last by done.
              rewrite -subnBA; last by done.
              by rewrite addn1 ltnS.
            }
          Qed.

        End InterferenceSingleJob.

        (* Next, consider the other case where there are at least two jobs:
           the first job j_fst, and the last job j_lst. *)
        Section InterferenceTwoOrMoreJobs.

          (* Assume there are at least two jobs. *)
          Variable num_mid_jobs: nat.
          Hypothesis H_at_least_two_jobs : size sorted_jobs = num_mid_jobs.+2.

          (* Let j_lst be the last job of the sequence and a_lst its arrival time. *)
          Let j_lst := nth elem sorted_jobs num_mid_jobs.+1.
          Let a_lst := job_arrival j_lst.

          (* In this section, we prove some basic lemmas about the first and last jobs. *)
          Section FactsAboutFirstAndLastJobs.

            (* The last job is an interfering job of task tsk_k. *)
            Lemma interference_bound_edf_j_lst_is_job_of_tsk_k :
              arrives_in arr_seq j_lst /\
              job_task j_lst = tsk_k /\
              interference_caused_by j_lst t1 t2 != 0 /\
              j_lst \in jobs_scheduled_between sched t1 t2.
            Proof.
              apply interference_bound_edf_all_jobs_from_tsk_k, mem_nth.
              by rewrite H_at_least_two_jobs.
            Qed.

            (* The deadline of j_lst is the deadline of tsk_k. *)
            Lemma interference_bound_edf_j_lst_deadline :
              job_deadline j_lst = task_deadline tsk_k.
            Proof.
              unfold valid_sporadic_job in *.
              rename H_valid_job_parameters into PARAMS.
              have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
              destruct LST as [LSTarr [LSTtask _]].
              by specialize (PARAMS j_lst LSTarr); des; rewrite PARAMS1 LSTtask.
            Qed.

            (* The first job arrives before the last job. *)
            Lemma interference_bound_edf_j_fst_before_j_lst :
              job_arrival j_fst <= job_arrival j_lst.
            Proof.
              rename H_at_least_two_jobs into SIZE.
              unfold j_fst, j_lst; rewrite -[num_mid_jobs.+1]add0n.
              apply prev_le_next; last by rewrite SIZE leqnn.
              by intros i LT; apply interference_bound_edf_jobs_ordered_by_arrival.
            Qed.

            (* The last job arrives before the end of the interval. *)
            Lemma interference_bound_edf_last_job_arrives_before_end_of_interval :
              job_arrival j_lst < t2.
            Proof.
              rewrite leqNgt; apply/negP; unfold not; intro LT2.
              exploit interference_bound_edf_all_jobs_from_tsk_k.
              {
                apply mem_nth; instantiate (1 := num_mid_jobs.+1).
                by rewrite -(ltn_add2r 1) addn1 H_at_least_two_jobs addn1.
              }  
              instantiate (1 := elem); move => [LSTarr [LSTtsk [/eqP LSTserv LSTin]]].
              apply LSTserv; apply/eqP; rewrite -leqn0.
              apply leq_trans with (n := service_during sched j_lst t1 t2);
                first by apply job_interference_le_service.
              rewrite leqn0; apply/eqP; unfold service_during.
              by apply cumulative_service_before_job_arrival_zero with (job_arrival0 := job_arrival).
            Qed.

            (* Since there are multiple jobs, j_fst is far enough from the end of
               the interval that its response-time bound is valid
               (by the assumption H_all_previous_jobs_completed_on_time). *)
            Lemma interference_bound_edf_j_fst_completed_on_time :
              completed job_cost sched j_fst (a_fst + R_k).
            Proof.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k; des.
              set j_snd := nth elem sorted_jobs 1.
              exploit interference_bound_edf_all_jobs_from_tsk_k.
              {
                by apply mem_nth; instantiate (1 := 1); rewrite H_at_least_two_jobs.
              }
              instantiate (1 := elem); move => [SNDarr [SNDtsk [/eqP SNDserv _]]].
              apply H_all_previous_jobs_completed_on_time; try (by done).
              apply leq_ltn_trans with (n := job_arrival j_snd); last first.
              {
                rewrite ltnNge; apply/negP; red; intro BUG; apply SNDserv.
                apply/eqP; rewrite -leqn0; apply leq_trans with (n := service_during
                                                                          sched j_snd t1 t2);
                  first by apply job_interference_le_service.
                rewrite leqn0; apply/eqP.
                by apply cumulative_service_before_job_arrival_zero with (job_arrival0 := job_arrival).
              }
              apply leq_trans with (n := a_fst + p_k).
              {
                by rewrite leq_add2l; apply leq_trans with (n := D_k);
                  [by apply H_R_k_le_deadline | by apply H_constrained_deadlines].
              }
            
              (* Since jobs are sporadic, we know that the first job arrives
                 at least p_k units before the second. *)
              unfold p_k; rewrite -FST0.
              apply H_sporadic_tasks; try (by done); [| by rewrite SNDtsk | ]; last first.
              {
                apply interference_bound_edf_jobs_ordered_by_arrival.
                by rewrite H_at_least_two_jobs.
              }
              red; move => /eqP BUG.
              by rewrite nth_uniq in BUG; rewrite ?SIZE //;
                [ by apply interference_bound_edf_at_least_one_job
                | by rewrite H_at_least_two_jobs
                | by rewrite sort_uniq; apply filter_uniq, undup_uniq].
            Qed.

          End FactsAboutFirstAndLastJobs.

          (* Next, we prove that the distance between the first and last jobs is at least
             num_mid_jobs + 1 periods. *)
          Lemma interference_bound_edf_many_periods_in_between :
            a_lst - a_fst >= num_mid_jobs.+1 * p_k.
          Proof.
            unfold a_fst, a_lst, j_fst, j_lst. 
            assert (EQnk: num_mid_jobs.+1=(size sorted_jobs).-1).
              by rewrite H_at_least_two_jobs.
            rewrite EQnk telescoping_sum;
              last by ins; apply interference_bound_edf_jobs_ordered_by_arrival.
            rewrite -[_ * _ tsk_k]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
            rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
            apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.

            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth elem sorted_jobs i.
            set next := nth elem sorted_jobs i.+1.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
              by unfold cur, next; apply interference_bound_edf_jobs_ordered_by_arrival.
             
            feed (interference_bound_edf_all_jobs_from_tsk_k cur).
              by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs.
            intros [CURarr [CURtsk [_ CURin]]].

            feed (interference_bound_edf_all_jobs_from_tsk_k next).
              by apply mem_nth; destruct sorted_jobs.
            intros [NEXTarr [NEXTtsk [_ NEXTin]]].

            (* Use the sporadic task model to conclude that cur and next are separated
               by at least (task_period tsk) units. Of course this only holds if cur != next.
               Since we don't know much about the list (except that it's sorted), we must
               also prove that it doesn't contain duplicates. *)
            assert (CUR_LE_NEXT: job_arrival cur + task_period (job_task cur) <= job_arrival next).
            {
              apply H_sporadic_tasks; try (by done).
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/interfering_jobs filter_uniq // undup_uniq.
                by rewrite CURtsk.
            }
            by rewrite subh3 // addnC /p_k -CURtsk.
          Qed.

          Lemma interference_bound_edf_slack_le_delta:
            D_k - R_k <= D_i.
          Proof.
            have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
                interference_bound_edf_j_fst_completed_on_time.
            rewrite leq_subLR -(leq_add2r a_fst).
            rewrite -addnA [R_k + _]addnC -addnA.
            apply leq_trans with (n := D_i + t1);
              last by rewrite leq_add2l.
            have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
            destruct FST as [ARRfst [_ [ LEdl _]]].  
            apply interference_under_edf_implies_shorter_deadlines with
                (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LEdl; try (by done).
            rewrite addnC [D_i + _]addnC.
            unfold D_k, D_i.
            by rewrite -interference_bound_edf_j_fst_deadline
                       -interference_bound_edf_j_i_deadline.
          Qed.

          (* Using the lemma above, we prove that the ratio n_k is at least the number of
             middle jobs + 1, ... *)
          Lemma interference_bound_edf_n_k_covers_all_jobs :
            n_k >= num_mid_jobs.+2.
          Proof.
            have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
                interference_bound_edf_j_fst_completed_on_time.
            have SLACK := interference_bound_edf_slack_le_delta.
            rename H_valid_task_parameters into TASK_PARAMS,
                   H_tsk_k_in_task_set into INk.
            unfold valid_sporadic_taskset, is_valid_sporadic_task,
                   interference_bound, edf_specific_interference_bound in *.
            have DIST := interference_bound_edf_many_periods_in_between.
            rewrite leqNgt; apply/negP; unfold not; rewrite ltnS;  intro LTnk.
            assert (BUG: a_lst - a_fst > D_i + R_k - D_k).
            {
              apply leq_trans with (n := num_mid_jobs.+1 * p_k); last by done.
              apply leq_trans with (n := n_k * p_k);
                last by rewrite leq_mul2r; apply/orP; right.
              unfold n_k, div_ceil.
              feed (TASK_PARAMS tsk_k); [by done | des].
              destruct (p_k %| D_i + R_k - D_k + 1) eqn:DIV.
                - by rewrite dvdn_eq in DIV; move: DIV => /eqP DIV; rewrite DIV addn1.
                - by rewrite -addn1; apply ltnW, ltn_ceil.      
            }
            rewrite leq_subLR in SLACK.
            rewrite -(leq_add2r a_fst) subh1 in BUG;
              last by apply interference_bound_edf_j_fst_before_j_lst.
            rewrite -[a_lst + _ - _]subnBA // subnn subn0 in BUG.
            rewrite addnC addnS in BUG.
            rewrite addnBA // in BUG; last by rewrite addnC.
            rewrite -(ltn_add2r D_k) in BUG.
            rewrite subh1 in BUG; last first.
            {
              rewrite [D_i + R_k]addnC.
              by apply leq_trans with (n := R_k + D_i);
                last by apply leq_addl.
            }
            rewrite -addnBA // subnn addn0 in BUG.
            rewrite [D_i + _]addnC addnA in BUG.
            apply leq_ltn_trans with (m := t1 + D_i) in BUG;
              last by rewrite leq_add2r.
            have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
            destruct LST as [ARRlst [_ [ LEdl _]]].  
            apply interference_under_edf_implies_shorter_deadlines with
                  (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LEdl; try (by done).
            unfold D_i, D_k in DIST; rewrite interference_bound_edf_j_lst_deadline
                                             interference_bound_edf_j_i_deadline in LEdl.
            by rewrite ltnNge LEdl in BUG.
          Qed.

          (* ... which allows bounding the interference of the middle and last jobs
             using n_k multiplied by the cost. *)
          Lemma interference_bound_edf_holds_for_multiple_jobs :
            \sum_(0 <= i < num_mid_jobs.+2)
              interference_caused_by (nth elem sorted_jobs i) t1 t2
            <= interference_bound.
          Proof.
            apply leq_trans with (n := num_mid_jobs.+2 * task_cost tsk_k); last first.
            {
              rewrite leq_mul2r; apply/orP; right.
              by apply interference_bound_edf_n_k_covers_all_jobs.
            }
            {
              apply leq_trans with (n := \sum_(0 <= i < num_mid_jobs.+2) task_cost tsk_k);
                last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
              rewrite big_nat_cond [\sum_(0 <= i < _ | true) _]big_nat_cond.
              apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite H_at_least_two_jobs.
            }
          Qed.

        End InterferenceTwoOrMoreJobs.

      End InterferenceManyJobs.
      
      Theorem interference_bound_edf_bounds_interference :
        x <= interference_bound.
      Proof.
        (* Use the definition of workload based on list of jobs. *)
        apply (leq_trans interference_bound_edf_use_another_definition). 

        (* We only care about the jobs that cause interference. *)
        rewrite interference_bound_edf_simpl_by_filtering_interfering_jobs.

        (* Now we order the list by job arrival time. *)
        rewrite interference_bound_edf_simpl_by_sorting_interfering_jobs.

        (* Next, we show that the workload bound holds if n_k
           is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM;
          first by apply interference_bound_edf_holds_for_at_most_n_k_jobs.
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Find some dummy element to use in the nth function *)
        assert (EX: exists elem: Job, True).
          destruct sorted_jobs as [| j]; [by rewrite ltn0 in NUM | by exists j].
        destruct EX as [elem _].

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First, we show that the bound holds for an empty list of jobs. *)
        destruct (size sorted_jobs) as [| n] eqn:SIZE;
          first by rewrite big_geq.

        (* Then, we show the same for a single job, or for multiple jobs. *)
        destruct n as [| num_mid_jobs].
        {
          rewrite big_nat_recr // big_geq //.
          rewrite [nth]lock /= -lock add0n.
          by apply interference_bound_edf_holds_for_a_single_job; rewrite SIZE.
        }
        {
          by apply interference_bound_edf_holds_for_multiple_jobs; first by rewrite SIZE.
        }
      Qed.
      
    End MainProof.
    
  End ProofSpecificBound.

  (* As required by the proof of convergence of EDF RTA, we show that the
     EDF-specific bound is monotonically increasing with both the size
     of the interval and the value of the previous response-time bounds. *)
  Section MonotonicitySpecificBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Variable tsk tsk_other: sporadic_task.
    Hypothesis H_period_positive: task_period tsk_other > 0.

    Variable delta delta' R R': time.
    Hypothesis H_delta_monotonic: delta <= delta'.
    Hypothesis H_response_time_monotonic: R <= R'.
    Hypothesis H_cost_le_rt_bound: task_cost tsk_other <= R.

    Lemma interference_bound_edf_monotonic :
      interference_bound_edf task_cost task_period task_deadline tsk delta (tsk_other, R) <=
      interference_bound_edf task_cost task_period task_deadline tsk delta' (tsk_other, R').
    Proof.
      rename H_response_time_monotonic into LEr, H_delta_monotonic into LEx,
             H_cost_le_rt_bound into LEcost, H_period_positive into GEperiod.
      unfold interference_bound_edf, interference_bound_generic.
      rewrite leq_min; apply/andP; split.
      {
        apply leq_trans with (n := W task_cost task_period (fst (tsk_other, R))
                                     (snd (tsk_other, R)) delta);
          [by apply geq_minl | by apply W_monotonic].
      }
      {
        apply leq_trans with (n := edf_specific_interference_bound task_cost task_period
                                                          task_deadline tsk tsk_other R);
          first by apply geq_minr.
        unfold edf_specific_interference_bound; simpl.
        rewrite leq_mul2r; apply/orP; right.
        apply leq_divceil2r; first by done.
        by rewrite leq_add2r leq_sub2r // leq_add2l.
      }
    Qed.

  End MonotonicitySpecificBound.

End InterferenceBoundEDF.