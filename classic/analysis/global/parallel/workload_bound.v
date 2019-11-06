Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.global.response_time rt.model.schedule.global.workload
               rt.model.schedule.global.schedulability.
Require Import rt.model.schedule.global.basic.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.

Module WorkloadBound.
  
  Import Job SporadicTaskset Schedule ScheduleOfSporadicTask TaskArrival ResponseTime Schedulability Workload.

  Section WorkloadBoundDef.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    
    Variable tsk: sporadic_task.
    Variable R_tsk: time. (* Known response-time bound for the task *)
    Variable delta: time. (* Length of the interval *)
    
    (* Bound on the number of jobs that execute on the interval *)
    Definition max_jobs :=
      div_ceil (delta + R_tsk) (task_period tsk).

    (* Simplified workload bound for parallel jobs.*)
    Definition W := max_jobs * task_cost tsk.

  End WorkloadBoundDef.
  
  Section BasicLemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.

    (* Let tsk be any task...*)
    Variable tsk: sporadic_task.

    (* ...with period > 0. *)
    Hypothesis H_period_positive: task_period tsk > 0.

    (* Let R1 <= R2 be two response-time bounds that
       are larger than the cost of the tsk. *)
    Variable R1 R2: time.
    Hypothesis H_R_lower_bound: R1 >= task_cost tsk.
    Hypothesis H_R1_le_R2: R1 <= R2.
      
    Let workload_bound := W task_cost task_period tsk.

    (* The workload bound W is monotonically increasing. *)
    Lemma W_monotonic :
      forall t1 t2,
        t1 <= t2 ->
        workload_bound R1 t1 <= workload_bound R2 t2.
    Proof.
      intros t1 t2 LEt.
      unfold workload_bound, W, max_jobs.
      rewrite leq_mul2r; apply/orP; right.
      by apply leq_divceil2r; last by apply leq_add.
    Qed.

  End BasicLemmas.
 
  Section ProofWorkloadBound.
 
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_deadline: Job -> time.

    Variable arr_seq: arrival_sequence Job.

    (* Assume that all jobs have valid parameters *)
    Hypothesis H_jobs_have_valid_parameters :
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    (* Consider any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
    (* Assumption: jobs only execute if they arrived.
       This is used to eliminate jobs that arrive after end of the interval t1 + delta. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.

    (* Assumption: jobs do not execute after they completed.
       This is used to eliminate jobs that complete before the start of the interval t1. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Assumption: sporadic task model.
       This is necessary to conclude that consecutive jobs ordered by arrival times
       are separated by at least 'period' times units. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.

    (* Before starting the proof, let's give simpler names to the definitions. *)
    Let job_has_completed_by := completed job_cost sched.

    Let workload_of (tsk: sporadic_task) (t1 t2: time) :=
      workload job_task sched tsk t1 t2.

    (* Now we define the theorem. Let tsk be any task in the taskset. *)
    Variable tsk: sporadic_task.

    (* Assumption: the task must have valid parameters:
         a) period > 0 (used in divisions)
         b) deadline of the jobs = deadline of the task
         c) cost <= period
            (used to prove that the distance between the first and last
             jobs is at least (cost + n*period), where n is the number
             of middle jobs. If cost >> period, the claim does not hold
             for every task set. *)
    Hypothesis H_valid_task_parameters:
      is_valid_sporadic_task task_cost task_period task_deadline tsk.

    (* Consider an interval [t1, t1 + delta). *)
    Variable t1 delta: time.

    (* Assume that any job with response-time bound R_tsk before
       t1 + delta indeed completes within the response-time bound. *)
    Variable R_tsk: time.

    Hypothesis H_response_time_bound :    
      forall j,
        arrives_in arr_seq j ->
        job_task j = tsk ->
        job_arrival j + R_tsk < t1 + delta ->
        job_has_completed_by j (job_arrival j + R_tsk).
    
    Section MainProof.

      (* In this section, we prove that the workload of a task in the
         interval [t1, t1 + delta) is bounded by W. *)

      (* Let's simplify the names a bit. *)
      Let t2 := t1 + delta.
      Let n_k := max_jobs task_period tsk R_tsk delta.
      Let workload_bound := W task_cost task_period tsk R_tsk delta.
      
      (* Since we only care about the workload of tsk, we restrict
         our view to the set of jobs of tsk scheduled in [t1, t2). *)
      Let scheduled_jobs :=
        jobs_of_task_scheduled_between job_task sched tsk t1 t2.

      (* Now, let's consider the list of interfering jobs sorted by arrival time. *)
      Let earlier_arrival := fun x y => job_arrival x <= job_arrival y.
      Let sorted_jobs := (sort earlier_arrival scheduled_jobs).

      (* The first step consists in simplifying the sum corresponding
         to the workload. *)
      Section SimplifyJobSequence.

        (* After switching to the definition of workload based on a list
           of jobs, we show that sorting the list preserves the sum. *)
        Lemma workload_bound_simpl_by_sorting_scheduled_jobs :
          workload_joblist job_task sched tsk t1 t2 =
           \sum_(i <- sorted_jobs) service_during sched i t1 t2.
        Proof.
          unfold workload_joblist; fold scheduled_jobs.
          rewrite (eq_big_perm sorted_jobs) /= //.
          by rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Remember that both sequences have the same set of elements *)
        Lemma workload_bound_job_in_same_sequence :
          forall j,
            (j \in scheduled_jobs) = (j \in sorted_jobs).
        Proof.
          by apply perm_eq_mem; rewrite -(perm_sort earlier_arrival).
        Qed.

        (* Remember that all jobs in the sorted sequence is an
           interfering job of task tsk. *)
        Lemma workload_bound_all_jobs_from_tsk :
          forall j_i,
            j_i \in sorted_jobs ->
            arrives_in arr_seq j_i /\
            job_task j_i = tsk /\
            service_during sched j_i t1 t2 != 0 /\
            j_i \in jobs_scheduled_between sched t1 t2.
        Proof.
          rename H_jobs_come_from_arrival_sequence into FROMarr.
          intros j_i LTi.
          rewrite -workload_bound_job_in_same_sequence mem_filter in LTi; des.
          unfold jobs_scheduled_between in *; rewrite mem_undup in LTi0.
          apply mem_bigcat_nat_exists in LTi0; des.
          rewrite mem_scheduled_jobs_eq_scheduled in LTi0.
          repeat split; try (by done); first by apply (FROMarr j_i i). 
          {
            apply service_implies_cumulative_service with (t := i);
              first by apply/andP; split.
            by rewrite -not_scheduled_no_service negbK.
          }
          {
            rewrite mem_undup.
            apply mem_bigcat_nat with (j := i); first by auto.
            by rewrite mem_scheduled_jobs_eq_scheduled. 
          }
        Qed.

        (* Remember that consecutive jobs are ordered by arrival. *)
        Lemma workload_bound_jobs_ordered_by_arrival :
          forall i elem,
            i < (size sorted_jobs).-1 ->
            earlier_arrival (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1).
        Proof.
          intros i elem LT.
          assert (SORT: sorted earlier_arrival sorted_jobs).
            by apply sort_sorted; unfold total, earlier_arrival; ins; apply leq_total.
          by destruct sorted_jobs; simpl in *; [by rewrite ltn0 in LT | by apply/pathP].
        Qed.

      End SimplifyJobSequence.

      (* Next, we show that if the number of jobs is no larger than n_k,
         the workload bound trivially holds. *)
      Section WorkloadNotManyJobs.

        Lemma workload_bound_holds_for_at_most_n_k_jobs :
          size sorted_jobs <= n_k ->
          \sum_(i <- sorted_jobs) service_during sched i t1 t2 <=
            workload_bound.
        Proof.
          unfold workload_bound, W; intros LEnk.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk);
            last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
          rewrite [\sum_(_ <- _) service_during _ _ _ _]big_seq_cond.
          rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
          apply leq_sum; intros j_i; move/andP => [INi _].
          apply workload_bound_all_jobs_from_tsk in INi; des. 
          eapply cumulative_service_le_task_cost;
            [by apply H_completed_jobs_dont_execute | by apply INi0 |].
          by apply H_jobs_have_valid_parameters.
        Qed.

      End WorkloadNotManyJobs.

      (* Otherwise, assume that the number of jobs is larger than n_k >= 0.
         First, consider the simple case with only one job. *)
      Section WorkloadSingleJob.

        (* Assume that there's at least one job in the sorted list. *)
        Hypothesis H_at_least_one_job: size sorted_jobs > 0.

        Variable elem: Job.
        Let j_fst := nth elem sorted_jobs 0.

        (* The first job is an interfering job of task tsk. *)
        Lemma workload_bound_j_fst_is_job_of_tsk :
          arrives_in arr_seq j_fst /\
          job_task j_fst = tsk /\
          service_during sched j_fst t1 t2 != 0 /\
          j_fst \in jobs_scheduled_between sched t1 t2.
        Proof.
          by apply workload_bound_all_jobs_from_tsk, mem_nth.
        Qed.

        (* The workload bound holds for the single job. *)
        Lemma workload_bound_holds_for_a_single_job :
          \sum_(0 <= i < 1) service_during sched (nth elem sorted_jobs i) t1 t2 <=
          workload_bound.
        Proof.
          rename H_valid_task_parameters into PARAMS.
          unfold is_valid_sporadic_task in *.
          unfold workload_bound, W; fold n_k.
          have INfst := workload_bound_j_fst_is_job_of_tsk; des.
          rewrite big_nat_recr // big_geq // [nth]lock /= -lock add0n.
          apply leq_trans with (n := task_cost tsk).
          {
            eapply cumulative_service_le_task_cost; [by eauto 1 | by apply INfst0 |].
            by apply H_jobs_have_valid_parameters. 
          }
          rewrite -{1}[task_cost tsk]mul1n leq_mul2r; apply/orP; right.
          apply ceil_neq0; last by apply PARAMS0.
          {
            apply leq_trans with (n := delta); last by apply leq_addr.
            rewrite lt0n; apply/eqP; intro EQ0.
            move: INfst1 => /eqP BUG; apply BUG.
            unfold t2; rewrite EQ0 addn0.
            by unfold service_during; rewrite big_geq.
          }
        Qed.
        
      End WorkloadSingleJob.

      (* Next, consider the last case where there are at least two jobs:
         the first job j_fst, and the last job j_lst. *)
      Section WorkloadTwoOrMoreJobs.

        (* There are at least two jobs. *)
        Variable num_mid_jobs: nat.
        Hypothesis H_at_least_two_jobs : size sorted_jobs = num_mid_jobs.+2.
        
        Variable elem: Job.
        Let j_fst := nth elem sorted_jobs 0.
        Let j_lst := nth elem sorted_jobs num_mid_jobs.+1.

        (* The last job is an interfering job of task tsk. *)
        Lemma workload_bound_j_lst_is_job_of_tsk :
          arrives_in arr_seq j_lst /\
          job_task j_lst = tsk /\
          service_during sched j_lst t1 t2 != 0 /\
          j_lst \in jobs_scheduled_between sched t1 t2.
        Proof.
          apply workload_bound_all_jobs_from_tsk, mem_nth.
          by rewrite H_at_least_two_jobs.
        Qed.

        (* The response time of the first job must fall inside the interval. *)
        Lemma workload_bound_response_time_of_first_job_inside_interval :
          t1 <= job_arrival j_fst + R_tsk.
        Proof.
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          exploit workload_bound_all_jobs_from_tsk.
          {
            apply mem_nth; instantiate (1 := 0).
            apply ltn_trans with (n := 1); [by done | by rewrite H_at_least_two_jobs].
          }
          instantiate (1 := elem); move => [FSTarr [FSTtsk [/eqP FSTserv FSTin]]].
          apply FSTserv.
          apply (cumulative_service_after_job_rt_zero job_arrival job_cost) with (R := R_tsk);
            try (by done); last by apply ltnW.
          apply H_response_time_bound; try (by done).
          by apply leq_trans with (n := t1); last by apply leq_addr.
        Qed.

        (* The arrival of the last job must also fall inside the interval. *)
        Lemma workload_bound_last_job_arrives_before_end_of_interval :
          job_arrival j_lst < t2.
        Proof.
          rewrite leqNgt; apply/negP; unfold not; intro LT2.
          exploit workload_bound_all_jobs_from_tsk.
          {
            apply mem_nth; instantiate (1 := num_mid_jobs.+1).
            by rewrite -(ltn_add2r 1) addn1 H_at_least_two_jobs addn1.
          }  
          instantiate (1 := elem); move => [LSTarr [LSTtsk [/eqP LSTserv LSTin]]].
          unfold service_during; apply LSTserv.
          by eapply cumulative_service_before_job_arrival_zero; eauto 1.
        Qed.

        (* Bound the service of the middle jobs. *)
        Lemma workload_bound_service_of_middle_jobs :
          \sum_(0 <= i < num_mid_jobs)
            service_during sched (nth elem sorted_jobs i.+1) t1 t2 <=
            num_mid_jobs * task_cost tsk.
        Proof.
          apply leq_trans with (n := num_mid_jobs * task_cost tsk);
            last by rewrite leq_mul2l; apply/orP; right. 
          apply leq_trans with (n := \sum_(0 <= i < num_mid_jobs) task_cost tsk);
            last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
          rewrite big_nat_cond [\sum_(0 <= i < num_mid_jobs) task_cost _]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          exploit workload_bound_all_jobs_from_tsk.
          {
            instantiate (1 := nth elem sorted_jobs i.+1).
            apply mem_nth; rewrite H_at_least_two_jobs.
            by rewrite ltnS; apply leq_trans with (n := num_mid_jobs).
          }
          move => [ARR [TSK _]].
          eapply cumulative_service_le_task_cost; eauto 1.
          by apply H_jobs_have_valid_parameters.
        Qed.

        (* Conclude that the distance between first and last is at least num_mid_jobs + 1 periods. *)
        Lemma workload_bound_many_periods_in_between :
          job_arrival j_lst - job_arrival j_fst >= num_mid_jobs.+1 * (task_period tsk).
        Proof.
          assert (EQnk: num_mid_jobs.+1=(size sorted_jobs).-1).
            by rewrite H_at_least_two_jobs.
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum;
            last by ins; apply workload_bound_jobs_ordered_by_arrival.
          rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.

          (* To simplify, call the jobs 'cur' and 'next' *)
          set cur := nth elem sorted_jobs i.
          set next := nth elem sorted_jobs i.+1.

          (* Show that cur arrives earlier than next *)
          assert (ARRle: job_arrival cur <= job_arrival next).
            by unfold cur, next; apply workload_bound_jobs_ordered_by_arrival.
             
          feed (workload_bound_all_jobs_from_tsk cur).
            by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs.
          intros [CURarr [CURtsk [_ CURin]]].

          feed (workload_bound_all_jobs_from_tsk next).
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
              by rewrite sort_uniq -/scheduled_jobs filter_uniq // undup_uniq.
              by rewrite CURtsk.   
          }
          by rewrite subh3 // addnC -CURtsk.
        Qed.

        (* Next, we prove that n_k covers every scheduled job, ... *)
        Lemma workload_bound_n_k_covers_all_jobs :
          n_k >= num_mid_jobs.+2.
        Proof.
          rename H_valid_task_parameters into PARAMS.
          unfold is_valid_sporadic_task in *; des.
          rewrite leqNgt; apply/negP; unfold not; intro LTnk.
          assert (DISTmax: job_arrival j_lst - job_arrival j_fst >= delta + R_tsk).
          {
            apply leq_trans with (n := num_mid_jobs.+1 * task_period tsk);
              last by apply workload_bound_many_periods_in_between.
            apply leq_trans with (n := n_k * task_period tsk);
              last by rewrite leq_mul2r; apply/orP; right.
            unfold n_k, max_jobs, div_ceil.
            destruct (task_period tsk %| delta + R_tsk) eqn:DIV.
            {
              rewrite dvdn_eq in DIV; move: DIV => /eqP DIV.
              by rewrite DIV.
            }
            by apply ltnW, ltn_ceil, PARAMS0.
          }
          rewrite <- leq_add2r with (p := job_arrival j_fst) in DISTmax.
          rewrite addnC subh1 in DISTmax; last first.
          {
            unfold j_fst, j_lst; rewrite -[_.+1]add0n.
            apply prev_le_next; last by rewrite H_at_least_two_jobs add0n leqnn.
            by ins; apply workload_bound_jobs_ordered_by_arrival.
          }
          rewrite -[job_arrival j_lst + _ - _]subnBA // subnn subn0 in DISTmax.
          rewrite [delta + _]addnC addnA in DISTmax.
          apply leq_trans with (m := t1 + delta) in DISTmax; last first.
          {
            rewrite leq_add2r.
            by apply workload_bound_response_time_of_first_job_inside_interval.
          }
          have LST := workload_bound_last_job_arrives_before_end_of_interval.
          by apply leq_ltn_trans with (m := t2) in LST; first by rewrite ltnn in LST.
        Qed.

        (* ... so the workload bound trivially holds. *)
        Lemma workload_bound_holds :
            \sum_(0 <= i < num_mid_jobs.+2)
             service_during sched (nth elem sorted_jobs i) t1 t2
          <= workload_bound.
        Proof.
          unfold workload_bound, W; fold n_k.
          have ALL := workload_bound_n_k_covers_all_jobs.
          apply leq_trans with (n := num_mid_jobs.+2 * task_cost tsk);
            last by rewrite leq_mul2r; apply/orP; right.
          apply leq_trans with (n := \sum_(0 <= i < num_mid_jobs.+2) task_cost tsk);
            last by rewrite big_const_nat iter_addn addn0 subn0 mulnC.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
          apply leq_sum; intro i; move => /andP [/andP [_ LEi] _].
          exploit workload_bound_all_jobs_from_tsk.
          {
            instantiate (1 := nth elem sorted_jobs i).
            by apply mem_nth; rewrite H_at_least_two_jobs.
          }
          move => [ARR [TSK _]].
          eapply cumulative_service_le_task_cost; eauto 1.
          by apply H_jobs_have_valid_parameters.
        Qed.

      End WorkloadTwoOrMoreJobs.

      (* Using the lemmas above, we prove the main theorem about the workload bound. *)
      Theorem workload_bounded_by_W :
        workload_of tsk t1 (t1 + delta) <= workload_bound.
      Proof.
        unfold workload_of, workload_bound, W in *; ins; des.
        fold n_k.

        (* Use the definition of workload based on list of jobs. *)
        rewrite workload_eq_workload_joblist.

        (* Now we order the list by job arrival time. *)
        rewrite workload_bound_simpl_by_sorting_scheduled_jobs.

        (* Next, we show that the workload bound holds if n_k
           is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM;
          first by apply workload_bound_holds_for_at_most_n_k_jobs.
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Find some dummy element to use in the nth function *)
        assert (EX: exists elem: Job, True).
          destruct sorted_jobs; [ by rewrite ltn0 in NUM | by exists s].
        destruct EX as [elem _].

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First, we show that the bound holds for an empty list of jobs. *)
        destruct (size sorted_jobs) as [| n] eqn:SIZE;
          first by rewrite big_geq.
        
        (* Then, we show the same for a singleton set of jobs. *)
        destruct n as [| num_mid_jobs];
          first by apply workload_bound_holds_for_a_single_job; rewrite SIZE.
        (* Since num_mid_jobs + 2 <= n_k >= num_mid_jobs + 2, the proof follows easily. *)
        by apply workload_bound_holds.
      Qed.

    End MainProof.
    
  End ProofWorkloadBound.

End WorkloadBound.