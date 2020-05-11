Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.arrival.basic.task_arrival prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.global.response_time prosa.classic.model.schedule.global.workload
               prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
               prosa.classic.model.schedule.global.basic.interference prosa.classic.model.schedule.global.basic.interference_edf.
Require Import prosa.classic.analysis.global.basic.workload_bound
               prosa.classic.analysis.global.basic.interference_bound.
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

    (* ... due to a different task tsk_other, with response-time bound R_other. *)
    Variable tsk_other: sporadic_task.
    Variable R_other: time.

    (* Bertogna and Cirinei define the following bound for task interference
       under EDF scheduling. *)
    Definition edf_specific_interference_bound :=
      let d_tsk := task_deadline tsk in
      let e_other := task_cost tsk_other in
      let p_other := task_period tsk_other in
      let d_other := task_deadline tsk_other in
        (div_floor d_tsk p_other) * e_other +
        minn e_other ((d_tsk %% p_other) - (d_other - R_other)).

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
      Let basic_interference_bound := interference_bound_generic task_cost task_period tsk delta tsk_R.

      (* ... with and EDF-specific interference bound, ... *)
      Let edf_specific_bound := edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other.

      (* ... Bertogna and Cirinei define the following interference bound
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
    Variable arr_seq: arrival_sequence Job.

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
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    (* Also assume that jobs are sequential and that there exists at
       least one processor. *)
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Consider a task set ts where all jobs come from the task set
       and tasks have valid parameters and constrained deadlines. *)
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
    
    (* ... and j_i one of its jobs. *)
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
        task_interference job_arrival job_cost job_task sched j_i tsk_k
                          (job_arrival j_i) (job_arrival j_i + delta).

      (* Also, recall the EDF-specific interference bound for EDF. *)
      Let interference_bound :=
        edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k.

      (* Let's simplify the names a bit. *)
      Let t1 := job_arrival j_i.
      Let t2 := job_arrival j_i + delta.
      Let D_i := task_deadline tsk_i.
      Let D_k := task_deadline tsk_k.
      Let p_k := task_period tsk_k.

      Let n_k := div_floor D_i p_k.

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

      (* Now we proceed with the proof. The first step consists in simplifying the sum corresponding to the workload. *)
      Section SimplifyJobSequence.

        (* Use the alternative definition of task interference, based on
           individual job interference. *)
        Lemma interference_bound_edf_use_another_definition :
          x <= \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_k)
                interference_caused_by j t1 t2.
        Proof.
          apply interference_le_interference_joblist.
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
          by rewrite (perm_big sorted_jobs) /=; last by rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Note that both sequences have the same set of elements. *)
        Lemma interference_bound_edf_job_in_same_sequence :
          forall j,
            (j \in interfering_jobs) = (j \in sorted_jobs).
        Proof.
          by apply perm_mem; rewrite -(perm_sort earlier_arrival).
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
          rename H_jobs_come_from_arrival_sequence into FROMarr.
          intros j LTi.
          rewrite -interference_bound_edf_job_in_same_sequence mem_filter in LTi; des.
          have IN := LTi0.
          unfold jobs_scheduled_between in *; rewrite mem_undup in IN.
          apply mem_bigcat_nat_exists in IN; des.
          rewrite mem_scheduled_jobs_eq_scheduled in IN.
          repeat split; try (by done).
          by apply (FROMarr j i).
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

        (* Finally, for any job of task tsk_k, the interference is bounded by the task cost. *)
        Lemma interference_bound_edf_interference_le_task_cost :
          forall j,
            j \in interfering_jobs ->
            interference_caused_by j t1 t2 <= task_cost tsk_k.
        Proof.
          rename H_valid_job_parameters into PARAMS.
          intros j IN.
          feed (interference_bound_edf_all_jobs_from_tsk_k j);
            first by rewrite -interference_bound_edf_job_in_same_sequence.
          move => [ARRj [TSKj _]].
          apply leq_trans with (n := service_during sched j t1 t2);
            first by apply job_interference_le_service.
          apply cumulative_service_le_task_cost with (job_task0 := job_task)
            (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline);
            try (by done).
          by apply PARAMS.
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
          rewrite -[\sum_(_ <- _ | _) _]addn0 leq_add //.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk_k);
            last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
          {
            rewrite [\sum_(_ <- _) interference_caused_by _ _ _]big_seq_cond.
            rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
            apply leq_sum; intros i; move/andP => [INi _].
            rewrite -interference_bound_edf_job_in_same_sequence in INi.
            by apply interference_bound_edf_interference_le_task_cost.
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
            destruct FST as [FSTarr [_ [ FSTserv _]]].
            move: FSTserv => /negP FSTserv; apply FSTserv.
            rewrite -leqn0; apply leq_trans with (n := service_during sched j_fst t1 t2);
              first by apply job_interference_le_service.
            rewrite leqn0; apply/eqP.
            by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k)
              (job_arrival0 := job_arrival); try (by done); apply ltnW.
          Qed. 
          
        End FactsAboutFirstJob.
        
        (* Now, let's prove the interference bound for the particular case of a single job.
           This case must be solved separately because the single job can simultaneously
           be carry-in and carry-out job, so its response time is not necessarily
           bounded by R_k (from the hypothesis H_all_previous_jobs_completed_on_time). *)
        Section InterferenceSingleJob.

          (* Assume that there's at least one job in the sorted list. *)
          Hypothesis H_only_one_job: size sorted_jobs = 1.
          
          (* Since there's only one job, we simplify the terms in the interference bound. *)
          Lemma interference_bound_edf_simpl_when_there's_one_job :
            D_i %% p_k - (D_k - R_k) = D_i - (D_k - R_k).
          Proof.
            rename H_many_jobs into NUM,
                   H_valid_task_parameters into TASK_PARAMS,
                   H_tsk_k_in_task_set into INk.
            unfold valid_sporadic_taskset, is_valid_sporadic_task,
                   interference_bound, edf_specific_interference_bound in *.
            rewrite H_only_one_job in NUM.
            rewrite ltnS leqn0 in NUM; move: NUM => /eqP EQnk.
            move: EQnk => /eqP EQnk; unfold n_k, div_floor in EQnk.
            rewrite -leqn0 leqNgt divn_gt0 in EQnk;
              last by specialize (TASK_PARAMS tsk_k INk); des.
            by rewrite -ltnNge in EQnk; rewrite modn_small //.
          Qed.

          (* Next, we show that if j_fst completes by its response-time bound R_k,
             then then interference bound holds. *)
          Section ResponseTimeOfSingleJobBounded.

            Hypothesis H_j_fst_completed_by_rt_bound :
              completed job_cost sched j_fst (a_fst + R_k).
            
            Lemma interference_bound_edf_holds_for_single_job_that_completes_on_time :
              job_interference job_arrival job_cost sched j_i j_fst t1 t2 <= D_i - (D_k - R_k).
            Proof.
              rename H_j_fst_completed_by_rt_bound into RBOUND.
              have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval RBOUND.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [FSTarr [_ [ LEdl _]]].            
              apply interference_under_edf_implies_shorter_deadlines with
                    (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LEdl; try (by done).
              destruct (D_k - R_k <= D_i) eqn:LEdk; last first.
              {
                apply negbT in LEdk; rewrite -ltnNge in LEdk.
                apply leq_trans with (n := 0); last by done.
                apply leq_trans with (n := job_interference job_arrival job_cost sched j_i j_fst
                                                                        (a_fst + R_k) t2).
                {
                  apply extend_sum; last by apply leqnn.
                  rewrite -(leq_add2r D_i).
                  rewrite interference_bound_edf_j_fst_deadline
                          interference_bound_edf_j_i_deadline in LEdl.
                  apply leq_trans with (n := a_fst + D_k); last by done.
                  rewrite -addnA leq_add2l.
                  by apply ltnW; rewrite -ltn_subRL.
                }
                apply leq_trans with (n := service_during sched j_fst (a_fst + R_k) t2);
                  first by apply job_interference_le_service.
                unfold service_during; rewrite leqn0; apply/eqP.
                by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k)
                   (job_arrival0 := job_arrival); try (by done); apply leqnn.
              }
              {
                rewrite -(leq_add2r (D_k - R_k)) subh1 // -addnBA // subnn addn0.
                assert (SUBST: D_k - R_k = \sum_(a_fst + R_k <= i < a_fst + D_k) 1).
                {
                  rewrite big_const_nat iter_addn mul1n addn0.
                  rewrite addnC -subnBA; last by apply leq_addr.
                  by rewrite addnC -addnBA // subnn addn0.
                }
                apply leq_trans with (n := job_interference job_arrival job_cost sched j_i j_fst t1
                                                            (a_fst + D_k) + (D_k - R_k)).
                {
                  rewrite leq_add2r.
                  destruct (t2 <= a_fst + R_k) eqn:LEt2.
                  {
                    apply extend_sum; first by apply leqnn.
                    apply leq_trans with (n := a_fst + R_k); first by done.
                    by rewrite leq_add2l; apply H_R_k_le_deadline.
                  }
                  {
                    unfold job_interference.
                    apply negbT in LEt2; rewrite -ltnNge in LEt2.
                    rewrite -> big_cat_nat with (n := a_fst + R_k);
                      [simpl | by apply AFTERt1 | by apply ltnW].
                    apply leq_trans with (n := job_interference job_arrival job_cost sched j_i j_fst t1
                                 (a_fst + R_k) + service_during sched j_fst (a_fst + R_k) t2).
                    {
                      rewrite leq_add2l.
                      by apply job_interference_le_service.
                    }
                    unfold service_during.
                    rewrite -> cumulative_service_after_job_rt_zero with
                      (job_arrival0 := job_arrival) (job_cost0 := job_cost) (R := R_k); try (by done). 
                    rewrite addn0; apply extend_sum; first by apply leqnn.
                    by rewrite leq_add2l; apply H_R_k_le_deadline.
                  }
                }

                unfold job_interference.
                rewrite -> big_cat_nat with (n := a_fst + R_k);
                  [simpl| by apply AFTERt1 | by rewrite leq_add2l; apply H_R_k_le_deadline].
                apply leq_trans with (n := job_interference job_arrival job_cost sched j_i j_fst t1
                  (a_fst+R_k) + service_during sched j_fst (a_fst+R_k) (a_fst+D_k) + (D_k-R_k)).
                {
                  rewrite leq_add2r leq_add2l.
                  by apply job_interference_le_service.
                }
                unfold service_during.
                rewrite -> cumulative_service_after_job_rt_zero with
                  (job_arrival0 := job_arrival) (job_cost0 := job_cost) (R:=R_k); try (by done).
                rewrite addn0.
                apply leq_trans with (n := (\sum_(t1 <= t < a_fst + R_k) 1) +
                                           \sum_(a_fst + R_k <= t < a_fst + D_k) 1).
                {
                  apply leq_add; last by rewrite SUBST.
                  rewrite big_const_nat iter_addn mul1n addn0.
                  rewrite -{1}[a_fst + R_k](addKn t1) -addnBA //.
                  by apply job_interference_le_delta.
                }
                rewrite -big_cat_nat;
                  [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply H_R_k_le_deadline ].
                rewrite big_const_nat iter_addn mul1n addn0 leq_subLR.
                by unfold D_i, D_k, t1, a_fst; rewrite -interference_bound_edf_j_fst_deadline
                                                       -interference_bound_edf_j_i_deadline.
              }    
            Qed.

          End ResponseTimeOfSingleJobBounded.

          (* Else, if j_fst did not complete by its response-time bound, then
             we need a separate proof. *)
          Section ResponseTimeOfSingleJobNotBounded.

            Hypothesis H_j_fst_not_complete_by_rt_bound :
              ~~ completed job_cost sched j_fst (a_fst + R_k).

            (* This trivially implies that a_fst + R_k lies after the end of the interval,
               otherwise j_fst would have completed by its response-time bound. *)
            Lemma interference_bound_edf_response_time_bound_of_j_fst_after_interval :
              job_arrival j_fst + R_k >= job_arrival j_i + delta.
            Proof.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [FSTarr [FSTtask _]].            
              rewrite leqNgt; apply/negP; intro LT.
              move: H_j_fst_not_complete_by_rt_bound => /negP BUG; apply BUG.
              by apply H_all_previous_jobs_completed_on_time.
            Qed.

            (* If the slack is too big (D_i < D_k - R_k), j_fst causes no interference. *)
            Lemma interference_bound_edf_holds_for_single_job_with_big_slack :
              D_i < D_k - R_k ->
              interference_caused_by j_fst t1 t2 = 0.
            Proof.
              intro LTdk.
              rewrite ltn_subRL in LTdk.
              rewrite -(ltn_add2l a_fst) addnA in LTdk.
              apply leq_ltn_trans with (m := t1 + D_i) in LTdk; last first.
              {
                rewrite leq_add2r.
                apply leq_trans with (n := t1 + delta); first by apply leq_addr.
                by apply interference_bound_edf_response_time_bound_of_j_fst_after_interval.
              }
              apply/eqP; rewrite -[_ _ _ _ == 0]negbK; apply/negP; red; intro BUG.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [FSTarr [_ [LEdl _]]].  
              apply interference_under_edf_implies_shorter_deadlines with
                     (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in BUG; try (by done).
              rewrite interference_bound_edf_j_fst_deadline
                      interference_bound_edf_j_i_deadline in BUG.
              by apply (leq_trans LTdk) in BUG; rewrite ltnn in BUG.
            Qed.

            (* Else, if the slack is small, j_fst causes interference for no longer than
               D_i - (D_k - R_k). *)
            Lemma interference_bound_edf_holds_for_single_job_with_small_slack :
              D_i >= D_k - R_k ->
              interference_caused_by j_fst t1 t2 <= D_i - (D_k - R_k).
            Proof.
              intro LEdk.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [FSTarr [FSTtask [LEdl _]]].            
              have LTr := interference_bound_edf_response_time_bound_of_j_fst_after_interval.
              apply subh3.
              apply leq_trans with (n := job_interference job_arrival job_cost sched j_i j_fst t1
                                                          (job_arrival j_fst + R_k) + (D_k - R_k));
                first by rewrite leq_add2r; apply extend_sum; [by apply leqnn|]. 
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 +
                                         \sum_(a_fst + R_k <= t < a_fst + D_k)1).
              {
                apply leq_add.
                {
                  rewrite big_const_nat iter_addn mul1n addn0.
                  rewrite -{1}[job_arrival j_fst + R_k](addKn t1) -addnBA;
                    first by apply job_interference_le_delta.
                  by apply leq_trans with (n := t1 + delta); first by apply leq_addr.
                }
                rewrite big_const_nat iter_addn mul1n addn0 addnC.
                rewrite -subnBA; last by apply leq_addr.
                by rewrite addnC -addnBA // subnn addn0.
              }
              rewrite -big_cat_nat; simpl; last 2 first.
              {
                apply leq_trans with (n := t1 + delta); first by apply leq_addr.
                by apply interference_bound_edf_response_time_bound_of_j_fst_after_interval.
              }  
              by rewrite leq_add2l; apply H_R_k_le_deadline.
              rewrite big_const_nat iter_addn mul1n addn0 leq_subLR.
              unfold D_i, D_k, t1, a_fst; rewrite -interference_bound_edf_j_fst_deadline
                                                  -interference_bound_edf_j_i_deadline.
              by apply interference_under_edf_implies_shorter_deadlines with
                (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LEdl.
            Qed.

          End ResponseTimeOfSingleJobNotBounded.
          
          (* By combining the results above, we prove that the interference caused by the single job
             is bounded by D_i - (D_k - R_k), ... *)
          Lemma interference_bound_edf_interference_of_j_fst_limited_by_slack :
            interference_caused_by j_fst t1 t2 <= D_i - (D_k - R_k).
          Proof.
            destruct (completed job_cost sched j_fst (a_fst + R_k)) eqn:COMP;
              first by apply interference_bound_edf_holds_for_single_job_that_completes_on_time. 
            apply negbT in COMP.
            destruct (ltnP D_i (D_k - R_k)) as [LEdk | LTdk].
              by rewrite interference_bound_edf_holds_for_single_job_with_big_slack.
              by apply interference_bound_edf_holds_for_single_job_with_small_slack.
          Qed.

          (* ... and thus the interference bound holds. *)
          Lemma interference_bound_edf_holds_for_a_single_job :
            interference_caused_by j_fst t1 t2 <= interference_bound.
          Proof.
            have ONE := interference_bound_edf_simpl_when_there's_one_job.
            have SLACK := interference_bound_edf_interference_of_j_fst_limited_by_slack.
            rename H_many_jobs into NUM, H_only_one_job into SIZE.
            unfold interference_caused_by, interference_bound, edf_specific_interference_bound.
            fold D_i D_k p_k n_k.
            rewrite SIZE ltnS leqn0 in NUM; move: NUM => /eqP EQnk.
            rewrite EQnk mul0n add0n.
            rewrite leq_min; apply/andP; split.
            {
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite SIZE.
            }
            by rewrite ONE; apply SLACK.
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

          (* Using the lemma above, we prove that the ratio n_k is at least the number of
             middle jobs + 1, ... *)
          Lemma interference_bound_edf_n_k_covers_middle_jobs_plus_one :
            n_k >= num_mid_jobs.+1.
          Proof.
            have DIST := interference_bound_edf_many_periods_in_between.
            have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
                interference_bound_edf_j_fst_completed_on_time.
            rename H_valid_task_parameters into TASK_PARAMS,
                   H_tsk_k_in_task_set into INk.
            unfold valid_sporadic_taskset, is_valid_sporadic_task,
                   interference_bound, edf_specific_interference_bound in *.
            rewrite leqNgt; apply/negP; unfold not; intro LTnk; unfold n_k in LTnk.
            rewrite ltn_divLR in LTnk; last by specialize (TASK_PARAMS tsk_k INk); des.
            apply (leq_trans LTnk) in DIST; rewrite ltn_subRL in DIST.
            rewrite -(ltn_add2r D_k) -addnA [D_i + _]addnC addnA in DIST. 
            apply leq_ltn_trans with (m := job_arrival j_i + D_i) in DIST; last first.
            {
              rewrite leq_add2r; apply (leq_trans AFTERt1).
              by rewrite leq_add2l; apply H_R_k_le_deadline.
            }
            have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
            destruct LST as [LSTarr [_ [ LEdl _]]].  
            apply interference_under_edf_implies_shorter_deadlines with
                  (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LEdl; try (by done).
            unfold D_i, D_k in DIST; rewrite interference_bound_edf_j_lst_deadline
                                             interference_bound_edf_j_i_deadline in LEdl.
            by rewrite ltnNge LEdl in DIST.
          Qed.

          (* ... which allows bounding the interference of the middle and last jobs
             using n_k multiplied by the cost. *)
          Lemma interference_bound_edf_holds_for_middle_and_last_jobs :
            interference_caused_by j_lst t1 t2 +
              \sum_(0 <= i < num_mid_jobs)
                interference_caused_by (nth elem sorted_jobs i.+1) t1 t2
            <= n_k * task_cost tsk_k.
          Proof.
            apply leq_trans with (n := num_mid_jobs.+1 * task_cost tsk_k); last first.
            {
              rewrite leq_mul2r; apply/orP; right.
              by apply interference_bound_edf_n_k_covers_middle_jobs_plus_one.
            }
            rewrite mulSn; apply leq_add.
            {
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite H_at_least_two_jobs.
            }
            {
              apply leq_trans with (n := \sum_(0 <= i < num_mid_jobs) task_cost tsk_k);
                last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
              rewrite big_nat_cond [\sum_(0 <= i < num_mid_jobs) task_cost _]big_nat_cond.
              apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              apply mem_nth; rewrite H_at_least_two_jobs.
              by rewrite ltnS; apply leq_trans with (n := num_mid_jobs).
            }
          Qed.

          (* Now, since n_k < sorted_jobs = num_mid_jobs + 2, it follows that
             n_k = num_mid_jobs + 1. *)
          Lemma interference_bound_edf_n_k_equals_num_mid_jobs_plus_one :
            n_k = num_mid_jobs.+1.
          Proof.
            have NK := interference_bound_edf_n_k_covers_middle_jobs_plus_one.
            rename H_many_jobs into NUM, H_at_least_two_jobs into SIZE.
            move: NK; rewrite leq_eqVlt orbC; move => /orP NK; des;
             [by rewrite SIZE ltnS leqNgt NK in NUM | by done].
          Qed.
          
          (* After proving the bounds of the middle and last jobs, we do the same for
             the first job. This requires a different proof in order to exploit the slack. *)
          Section InterferenceOfFirstJob.

            (* As required by the next lemma, in order to move (D_i %% p_k) to the left of
               the inequality (<=), we must show that it is no smaller than the slack. *)
            Lemma interference_bound_edf_remainder_ge_slack :
              D_k - R_k <= D_i %% p_k.
            Proof.
              have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
                interference_bound_edf_j_fst_completed_on_time.
              have NK := interference_bound_edf_n_k_equals_num_mid_jobs_plus_one.
              have DIST := interference_bound_edf_many_periods_in_between.
              rewrite -NK in DIST.
              rewrite -subndiv_eq_mod leq_subLR.
              fold (div_floor D_i p_k) n_k.
              rewrite addnBA; last by apply leq_trunc_div.
              apply leq_trans with (n := R_k + D_i - (a_lst - a_fst)); last by apply leq_sub2l.
              rewrite subnBA; last by apply interference_bound_edf_j_fst_before_j_lst.
              rewrite -(leq_add2r a_lst) subh1; last first.
              {
                apply leq_trans with (n := t2);
                  [by apply ltnW, interference_bound_edf_last_job_arrives_before_end_of_interval|].
                rewrite addnC addnA.
                apply leq_trans with (n := t1 + D_i).
                  unfold t2; rewrite leq_add2l; apply H_delta_le_deadline.
                by rewrite leq_add2r; apply AFTERt1.
              }
              rewrite -addnBA // subnn addn0 [D_k + _]addnC.
              apply leq_trans with (n := t1 + D_i);
                last by rewrite -addnA [D_i + _]addnC addnA leq_add2r addnC AFTERt1.
              have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
              destruct LST as [LSTarr [_ [ LSTserv _]]].
              unfold D_i, D_k, a_lst, t1; rewrite -interference_bound_edf_j_lst_deadline
                                                  -interference_bound_edf_j_i_deadline.
              by apply interference_under_edf_implies_shorter_deadlines with
                            (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LSTserv.
            Qed.

            (* To conclude that the interference bound holds, it suffices to show that
               this reordered inequality holds. *)
            Lemma interference_bound_edf_simpl_by_moving_to_left_side :
              interference_caused_by j_fst t1 t2 + (D_k - R_k) + D_i %/ p_k * p_k <= D_i ->
              interference_caused_by j_fst t1 t2 <= D_i %% p_k - (D_k - R_k).
            Proof.
              intro LE.
              apply subh3.
                by rewrite -subndiv_eq_mod; apply subh3.
            Qed.
              
            (* Next, we prove that interference caused by j_fst is bounded by the length
               of the interval [t1, a_fst + R_k), ... *)
            Lemma interference_bound_edf_interference_of_j_fst_bounded_by_response_time :
               interference_caused_by j_fst t1 t2 <= \sum_(t1 <= t < a_fst + R_k) 1.
            Proof.
              assert (AFTERt1: t1 <= a_fst + R_k).
              {
                apply interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval.
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
              destruct (leqP t2 (a_fst + R_k)) as [LEt2 | GTt2].
              {
                apply leq_trans with (n := job_interference job_arrival job_cost sched j_i j_fst t1
                                                                              (a_fst + R_k));
                  first by apply extend_sum; rewrite ?leqnn.
                simpl_sum_const; rewrite -{1}[_ + R_k](addKn t1) -addnBA //.
                by apply job_interference_le_delta.
              }
              {
                unfold interference_caused_by, job_interference.
                rewrite -> big_cat_nat with (n := a_fst + R_k);
                  [simpl | by apply AFTERt1 | by apply ltnW].
                rewrite -[\sum_(_ <= _ < _) 1]addn0; apply leq_add.
                {
                  simpl_sum_const; rewrite -{1}[_ + R_k](addKn t1) -addnBA //.
                  by apply job_interference_le_delta.
                }
                apply leq_trans with (n := service_during sched j_fst (a_fst + R_k) t2);
                  first by apply job_interference_le_service.
                rewrite leqn0; apply/eqP.
                apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k)
                  (job_arrival0 := job_arrival); [ by done | | by apply leqnn].
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
            Qed.

            (* ..., which leads to the following bounds based on interval lengths. *)
            Lemma interference_bound_edf_bounding_interference_with_interval_lengths :
              interference_caused_by j_fst t1 t2 + (D_k - R_k) + D_i %/ p_k * p_k <=
              \sum_(t1 <= t < a_fst + R_k) 1
              + \sum_(a_fst + R_k <= t < a_fst + D_k) 1
              + \sum_(a_fst + D_k <= t < a_lst + D_k) 1.
            Proof.
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + (D_k - R_k) +
                                                                       D_i %/ p_k * p_k).
              {
                rewrite 2!leq_add2r.
                apply interference_bound_edf_interference_of_j_fst_bounded_by_response_time.
              }
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + (D_k - R_k) +
                                                                        (a_lst - a_fst)).
              {
                rewrite leq_add2l; fold (div_floor D_i p_k) n_k.
                rewrite interference_bound_edf_n_k_equals_num_mid_jobs_plus_one.
                by apply interference_bound_edf_many_periods_in_between.
              }
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 +
                  \sum_(a_fst + R_k <= t < a_fst + D_k) 1 + \sum_(a_fst + D_k <= t < a_lst + D_k) 1).
              {
                by rewrite -2!addnA leq_add2l; apply leq_add;
                rewrite big_const_nat iter_addn mul1n addn0;
                rewrite ?subnDl ?subnDr leqnn.
              }
              by apply leqnn.
            Qed.

            (* To conclude, we show that the concatenation of these interval lengths equals
               (a_lst + D_k) - 1, ... *)
            Lemma interference_bound_edf_simpl_by_concatenation_of_intervals :
              \sum_(t1 <= t < a_fst + R_k) 1
              + \sum_(a_fst + R_k <= t < a_fst + D_k) 1
              + \sum_(a_fst + D_k <= t < a_lst + D_k) 1 = (a_lst + D_k) - t1.
            Proof.
              assert (AFTERt1: t1 <= a_fst + R_k).
              {
                apply interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval.
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
              rewrite -big_cat_nat;
                [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply H_R_k_le_deadline].
              rewrite -big_cat_nat; simpl; last 2 first.
              {
                apply leq_trans with (n := a_fst + R_k); first by apply AFTERt1.
                by rewrite leq_add2l; apply H_R_k_le_deadline.
              }
              {
                rewrite leq_add2r; unfold a_fst, a_lst, j_fst, j_lst.
                rewrite -[num_mid_jobs.+1]add0n; apply prev_le_next;
                  last by rewrite add0n H_at_least_two_jobs ltnSn.
                by ins; apply interference_bound_edf_jobs_ordered_by_arrival.
              }
              by rewrite big_const_nat iter_addn mul1n addn0.
            Qed.
            
            (* ... which results in proving that (a_lst + D_k) - t1 <= D_i.
               This holds because high-priority jobs have earlier deadlines. Therefore,
               the interference caused by the first job is bounded by D_i %% p_k - (D_k - R_k). *)
            Lemma interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack :
              interference_caused_by j_fst t1 t2 <= D_i %% p_k - (D_k - R_k).
            Proof.
              apply interference_bound_edf_simpl_by_moving_to_left_side.
              apply (leq_trans interference_bound_edf_bounding_interference_with_interval_lengths).
              rewrite interference_bound_edf_simpl_by_concatenation_of_intervals leq_subLR.
              have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
              destruct LST as [LSTarr [_ [ LSTserv _]]].
              unfold D_i, D_k, a_lst, t1; rewrite -interference_bound_edf_j_lst_deadline
                                                  -interference_bound_edf_j_i_deadline.
              by apply interference_under_edf_implies_shorter_deadlines
                with (arr_seq0 := arr_seq) (job_deadline0 := job_deadline) in LSTserv.
            Qed.

          End InterferenceOfFirstJob.

          (* Using the lemmas above we show that the interference bound works in the
             case of two or more jobs. *)
          Lemma interference_bound_edf_holds_for_multiple_jobs :
            \sum_(0 <= i < num_mid_jobs.+2)
              interference_caused_by (nth elem sorted_jobs i) t1 t2 <= interference_bound.
          Proof.
            (* Knowing that we have at least two elements, we take first and last out of the sum *) 
            rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
            rewrite addnA addnC addnA.

            have NK := interference_bound_edf_n_k_equals_num_mid_jobs_plus_one. 

            (* We use the lemmas we proved to show that the interference bound holds. *)
            unfold interference_bound, edf_specific_interference_bound.
            fold D_i D_k p_k n_k.
            rewrite addnC addnA; apply leq_add;
              first by rewrite addnC interference_bound_edf_holds_for_middle_and_last_jobs.
            rewrite leq_min; apply/andP; split.
            {
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite H_at_least_two_jobs.
            }
            by apply interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack.
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
        rewrite leq_min; apply/andP; split.
        apply leq_trans with (n :=  (minn (W task_cost task_period (fst (tsk_other, R))
                           (snd (tsk_other, R)) delta) (delta - task_cost tsk + 1)));
          first by apply geq_minl.
        apply leq_trans with (n := W task_cost task_period (fst (tsk_other, R))
                                                   (snd (tsk_other, R)) delta);
          [by apply geq_minl | by apply W_monotonic].
        apply leq_trans with (n := minn (W task_cost task_period (fst (tsk_other, R)) (snd (tsk_other, R)) delta) (delta - task_cost tsk + 1));
          first by apply geq_minl.
        apply leq_trans with (n := delta - task_cost tsk + 1);
          first by apply geq_minr.
        by rewrite leq_add2r leq_sub2r.
      }
      {
        apply leq_trans with (n := edf_specific_interference_bound task_cost task_period
                                                          task_deadline tsk tsk_other R);
          first by apply geq_minr.
        unfold edf_specific_interference_bound; simpl.
        rewrite leq_add2l leq_min; apply/andP; split; first by apply geq_minl.
        apply leq_trans with (n := task_deadline tsk %% task_period tsk_other -
                                   (task_deadline tsk_other - R));
          [by apply geq_minr | by rewrite 2?leq_sub2l 2?leq_sub2r // leq_sub2l].
      }
    Qed.

  End MonotonicitySpecificBound.

End InterferenceBoundEDF.