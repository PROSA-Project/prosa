Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.global.jitter.job rt.model.schedule.global.jitter.schedule
               rt.model.schedule.global.jitter.interference.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job SporadicTaskset ScheduleOfSporadicTaskWithJitter SporadicTaskset TaskArrival Interference Priority.

  Section Properties.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> time.
    
    (* Assume any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* Consider any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule Job num_cpus.

    (* For simplicity, let's define local names. *)
    Let job_is_backlogged := backlogged job_arrival job_cost job_jitter sched.
    
    Section Execution.

      (* A scheduler is work-conserving iff when a job j is backlogged,
         all processors are busy with other jobs.
         Note: backlogged means that jitter has already passed. *)
      Definition work_conserving :=
        forall j t,
          arrives_in arr_seq j ->
          job_is_backlogged j t ->
          forall cpu, exists j_other,
            scheduled_on sched j_other cpu t.

      (* We also provide an alternative, equivalent definition of work-conserving
         based on counting the number of scheduled jobs. *)
      Definition work_conserving_count :=
        forall j t,
          arrives_in arr_seq j ->
          job_is_backlogged j t ->
          size (jobs_scheduled_at sched t) = num_cpus.

    End Execution.

    Section FP.

      (* An FP policy ...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ... is respected by the schedule iff every scheduled
         job has higher (or same) priority than (as) a backlogged job. *)
      Definition respects_FP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          job_is_backlogged j t ->
          scheduled sched j_hp t ->
          higher_eq_priority (job_task j_hp) (job_task j).

    End FP.
    
    Section JLFP.

      (* A JLFP policy ...*)
      Variable higher_eq_priority: JLFP_policy Job.

      (* ... is respected by the schedule iff at any time t,
         a scheduled job has higher (or same) priority than (as)
         a backlogged job. *)
      Definition respects_JLFP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          job_is_backlogged j t ->
          scheduled sched j_hp t ->
          higher_eq_priority j_hp j.
      
    End JLFP.

    Section JLDP.

      (* A JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy Job.

      (* ... is respected by the schedule iff at any time t,
         a scheduled job has higher (or same) priority than (as)
         a backlogged job. *)
      Definition respects_JLDP_policy :=
        forall j j_hp t,
          arrives_in arr_seq j ->
          job_is_backlogged j t ->
          scheduled sched j_hp t ->
          higher_eq_priority t j_hp j.
      
    End JLDP.

    Section Lemmas.

      (* Assume all jobs have valid parameters, ...*)
      Hypothesis H_valid_job_parameters:
        forall j,
          arrives_in arr_seq j ->
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

      (* In this section, we prove that the two definitions of work-conserving are equivalent. *)
      Section EquivalentDefinitions.

        Lemma work_conserving_eq_work_conserving_count :
          work_conserving <-> work_conserving_count.
        Proof.
          unfold work_conserving, work_conserving_count; split.
          {
            intros EX j t ARRin BACK.
            specialize (EX j t ARRin BACK).
            apply eq_trans with (y := size (enum (processor num_cpus)));
              last by rewrite size_enum_ord.
            unfold jobs_scheduled_at.
            apply eq_trans with (y := size ((\cat_(cpu < num_cpus) map (fun x => Some x)
                                              (make_sequence (sched cpu t)))));
              first by rewrite -map_bigcat_ord size_map.
            apply eq_trans with (y := size (\cat_(cpu < num_cpus) [:: sched cpu t])).
            {
              f_equal; apply eq_bigr; intros cpu _.
              destruct (sched cpu t) eqn:SCHED; first by done.
              by specialize (EX cpu); des; move: EX => /eqP EX; rewrite EX in SCHED.
            }
            rewrite size_bigcat_ord.
            apply eq_trans with (y := \sum_(i < num_cpus) 1);
              last by rewrite big_const_ord iter_addn mul1n addn0 size_enum_ord.
            by apply eq_bigr.
          }
          {
            intros SIZE j t ARRin BACK cpu.
            specialize (SIZE j t ARRin BACK).
            destruct ([exists cpu, sched cpu t == None]) eqn:EX; last first.
            {
              apply negbT in EX; rewrite negb_exists in EX.
              move: EX => /forallP ALL; specialize (ALL cpu).
              destruct (sched cpu t) as [j0|] eqn:SOME; last by done.
              by exists j0; apply/eqP.
            }
            {
              move: EX => /existsP [cpu' /eqP EX].
              unfold jobs_scheduled_at in SIZE.
              move: SIZE => /eqP SIZE; rewrite -[size _ == _]negbK in SIZE.
              move: SIZE => /negP SIZE; exfalso; apply SIZE; clear SIZE.
              rewrite neq_ltn; apply/orP; left.
              rewrite size_bigcat_ord.
              rewrite -> big_mkord_ord with (x0 := 0).
              have MKORD := big_mkord (fun x => true); rewrite -MKORD.
              have CAT := big_cat_nat _ (fun x => true).
              rewrite -> CAT with (n := cpu'); [simpl | by done | by apply ltnW, ltn_ord].   
              assert (DIFF: exists k, num_cpus = (cpu' + k).+1).
              {
                exists (num_cpus - cpu').-1.
                rewrite -addnS prednK; last by rewrite ltn_subRL addn0 ltn_ord.
                rewrite addnBA; last by apply ltnW, ltn_ord.
                by rewrite addnC -addnBA // subnn addn0.
              } 
              des; rewrite {5}DIFF.
              rewrite big_nat_recl; last by apply leq_addr.
              apply leq_trans with (n := (\sum_(0 <= i < cpu') 1) + 1 +
                                         (\sum_(cpu' <= i < cpu' + k) 1));
                last first.
              {
                rewrite 2!big_const_nat 2!iter_addn 2!mul1n addn0 subn0.
                rewrite [cpu' + k]addnC -addnBA // subnn 2!addn0.
                by rewrite -addnA [1 + k]addnC addnA addn1 -DIFF.
              }
              {
                rewrite -addn1 addnC [_ + 1]addnC -addnA.
                apply leq_add; first by done.
                rewrite eq_fun_ord_to_nat; unfold make_sequence at 2; rewrite EX /= add0n. 
                apply leq_add; apply leq_sum; ins; unfold fun_ord_to_nat; des_eqrefl; try done;
                by unfold make_sequence; desf.
              }
            }
          }
        Qed.
          
      End EquivalentDefinitions.

    End Lemmas.

  End Properties.
  
End Platform.