Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.job
               prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.priority.
Require Import prosa.classic.model.schedule.uni.service
               prosa.classic.model.schedule.uni.workload
               prosa.classic.model.schedule.uni.schedule.
Require Import prosa.classic.model.arrival.curves.bounds. 
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

Module MaxArrivalsWorkloadBound.

  Import Job ArrivalCurves TaskArrival Priority UniprocessorSchedule Workload Service. 
         
  Section Lemmas.
    
    Context {Task: eqType}.
    Variable task_cost: Task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any arrival sequence with consistent, non-duplicate arrivals. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_times_are_consistent: arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
    
    (* Next, consider any uniprocessor schedule of this arrival sequence. *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* Consider an FP policy that indicates a higher-or-equal priority relation. *)
    Variable higher_eq_priority: FP_policy Task.
    Let jlfp_higher_eq_priority := FP_to_JLFP job_task higher_eq_priority.
    
    (* For simplicity, let's define some local names. *)
    Let arrivals_between := jobs_arrived_between arr_seq.
     
    (* We define the notion of request bound function. *)
    Section RequestBoundFunction.
      
      (* Let max_arrivals denote any function that takes a task and an interval length
         and returns the associated number of job arrivals of the task. *) 
      Variable max_arrivals: Task -> time -> nat.
      
      (* In this section, we define a bound for the workload of a single task
         under uniprocessor FP scheduling. *)
      Section SingleTask.

        (* Consider any task tsk that is to be scheduled in an interval of length delta. *)
        Variable tsk: Task.
        Variable delta: time.

        (* We define the following workload bound for the task. *)
        Definition task_request_bound_function := task_cost tsk * max_arrivals tsk delta.

      End SingleTask.

      (* In this section, we define a bound for the workload of multiple tasks. *)
      Section AllTasks.

        (* Consider a task set ts... *)
        Variable ts: list Task.

        (* ...and let tsk be any task in task set. *)
        Variable tsk: Task.
        
        (* Let delta be the length of the interval of interest. *)
        Variable delta: time.
        
        (* Recall the definition of higher-or-equal-priority task and
           the per-task workload bound for FP scheduling. *)
        Let is_hep_task tsk_other := higher_eq_priority tsk_other tsk.
        Let is_other_hep_task tsk_other := higher_eq_priority tsk_other tsk && (tsk_other != tsk).

        (* Using the sum of individual workload bounds, we define the following bound
           for the total workload of tasks in any interval of length delta. *)
        Definition total_request_bound_function :=
          \sum_(tsk <- ts) task_request_bound_function tsk delta.
        
        (* Similarly, we define the following bound for the total workload of tasks of 
           higher-or-equal priority (with respect to tsk) in any interval of length delta. *)
        Definition total_hep_request_bound_function_FP :=
          \sum_(tsk_other <- ts | is_hep_task tsk_other)
           task_request_bound_function tsk_other delta.
        
        (* We also define bound for the total workload of higher-or-equal priority 
           tasks other than tsk in any interval of length delta. *)
        Definition total_ohep_request_bound_function_FP :=
          \sum_(tsk_other <- ts | is_other_hep_task tsk_other)
           task_request_bound_function tsk_other delta.
        
      End AllTasks.
      
    End RequestBoundFunction.

    (* In this section we prove some lemmas about request bound functions. *)
    Section ProofWorkloadBound.

      (* Consider a task set ts... *)
      Variable ts: list Task.

      (* ...and let tsk be any task in ts. *)
      Variable tsk: Task.
      Hypothesis H_tsk_in_ts: tsk \in ts.

      (* Assume that a job cost cannot be larger than a task cost. *)
      Hypothesis H_job_cost_le_task_cost:
        forall j,
          arrives_in arr_seq j ->
          job_cost_le_task_cost task_cost job_cost job_task j.

      (* Next, we assume that all jobs come from the task set. *)
      Hypothesis H_all_jobs_from_taskset:
        forall j, arrives_in arr_seq j -> job_task j \in ts.

      (* Let max_arrivals be any arrival bound for taskset ts. *)
      Variable max_arrivals: Task -> time -> nat.
      Hypothesis H_is_arrival_bound:
        is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts. 
      
      (* Let's define some local names for clarity. *)
      Let task_rbf := task_request_bound_function max_arrivals tsk.
      Let total_rbf := total_request_bound_function max_arrivals ts.
      Let total_hep_rbf := total_hep_request_bound_function_FP max_arrivals ts tsk.
      Let total_ohep_rbf := total_ohep_request_bound_function_FP max_arrivals ts tsk.

      (* Next, we consider any job j of tsk. *)
      Variable j: Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.
      
      (* We define whether two jobs j1 and j2 are from the same task. *)
      Let same_task j1 j2 := job_task j1 == job_task j2.
      
      (* Next, we say that two jobs j1 and j2 are in relation other_higher_eq_priority, iff 
         j1 has higher or equal priority than j2 and is produced by a different task. *)
      Let other_higher_eq_priority j1 j2 := jlfp_higher_eq_priority j1 j2 && (~~ same_task j1 j2).

      (* Next, we recall the notions of total workload of jobs... *)
      Let total_workload t1 t2 :=
        workload_of_jobs job_cost (arrivals_between t1 t2) (fun j => true).
      
      (* ...notions of workload of higher or equal priority jobs... *)
      Let total_hep_workload t1 t2 :=
        workload_of_jobs job_cost (arrivals_between t1 t2)
                         (fun j_other => jlfp_higher_eq_priority j_other j).
      
      (* ... workload of other higher or equal priority jobs... *)
      Let total_ohep_workload t1 t2 :=
        workload_of_jobs job_cost (arrivals_between t1 t2)
                         (fun j_other => other_higher_eq_priority j_other j).

      (* ... and the workload of jobs of the same task as job j. *)
      Let task_workload (t1: time) (t2: time) :=
        workload_of_jobs job_cost (arrivals_between t1 t2)
                         (fun j_other => same_task j_other j).
      
      (* In this section we prove that the workload of any jobs is 
         no larger than the request bound function. *) 
      Section WorkloadIsBoundedByRBF.

        (* Consider any time t and any interval of length delta. *)
        Variable t: time.
        Variable delta: time.

        (* First, we prove that workload of task is no larger 
           than task request bound function. *)
        Lemma task_workload_le_task_rbf:
          task_workload t (t + delta) <= task_rbf delta.
        Proof.
          unfold task_workload.
          unfold task_rbf, task_request_bound_function.
          unfold is_arrival_bound in *.
          unfold arrivals_between.

          set l := jobs_arrived_between arr_seq t delta. 
          apply leq_trans with (
            task_cost tsk * num_arrivals_of_task job_task arr_seq tsk t (t + delta)).
          {
            rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
            rewrite -/l /workload_of_jobs.
            rewrite /is_job_of_task /same_task H_job_of_tsk muln1.
            apply leq_sum_seq; move => j0 IN0 /eqP EQ.
            rewrite -EQ.
            apply H_job_cost_le_task_cost.
              by apply in_arrivals_implies_arrived in IN0.
          }
          {
            rewrite leq_mul2l; apply/orP; right.
            rewrite -{2}[delta](addKn t).
            apply H_is_arrival_bound; first by done.
              by rewrite leq_addr.
          }
        Qed.

        (* Next, we prove that total workload of tasks is no larger 
             than total request bound function. *)
        Lemma total_workload_le_total_rbf:
          total_ohep_workload t (t + delta) <= total_ohep_rbf delta.
        Proof.
          rewrite /total_ohep_rbf /total_ohep_request_bound_function_FP
                  /task_request_bound_function.
          rewrite /total_ohep_workload /workload_of_jobs
                  /other_higher_eq_priority.
          rewrite /jlfp_higher_eq_priority
                  /FP_to_JLFP /same_task H_job_of_tsk. 
          rewrite /arrivals_between.
          
          set l := jobs_arrived_between arr_seq t (t + delta).
          set hep := higher_eq_priority.
          
          apply leq_trans with
          (\sum_(tsk' <- ts | hep tsk' tsk && (tsk' != tsk))
            (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
          {
            intros.
            have EXCHANGE :=
              exchange_big_dep
                (fun x => hep (job_task x) tsk && (job_task x != tsk)).
            rewrite EXCHANGE /=; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
            rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
            apply leq_sum; move => j0 /andP [IN0 HP0].
            rewrite big_mkcond (big_rem (job_task j0)) /=;
                    first by rewrite HP0 andTb eq_refl; apply leq_addr.
              by apply in_arrivals_implies_arrived in IN0;
              apply H_all_jobs_from_taskset.
          }
          apply leq_sum_seq; intros tsk0 INtsk0 HP0.
          apply leq_trans with (
            task_cost tsk0 * num_arrivals_of_task job_task arr_seq tsk0 t (t + delta)).
          {
            rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
            rewrite -/l /workload_of_jobs.
            rewrite /is_job_of_task  muln1.
            apply leq_sum_seq; move => j0 IN0 /eqP EQ.
            rewrite -EQ.
            apply H_job_cost_le_task_cost.
              by apply in_arrivals_implies_arrived in IN0.
          }
          {
            rewrite leq_mul2l; apply/orP; right.
            rewrite -{2}[delta](addKn t).
            apply H_is_arrival_bound; first by done.
              by rewrite leq_addr.
          }
        Qed.

        Lemma total_workload_le_total_rbf':
          total_hep_workload t (t + delta) <= total_hep_rbf delta.
        Proof.
          intros.
          rewrite /total_hep_rbf /total_hep_request_bound_function_FP
                  /task_request_bound_function.
          rewrite /total_hep_workload /workload_of_jobs
                  /jlfp_higher_eq_priority /FP_to_JLFP /same_task H_job_of_tsk. 
          rewrite /arrivals_between.
          
          set l := jobs_arrived_between arr_seq t (t + delta).
          set hep := higher_eq_priority.
          
          apply leq_trans with
          (n := \sum_(tsk' <- ts | hep tsk' tsk)
                 (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
          {
            intros.
            have EXCHANGE := exchange_big_dep (fun x => hep (job_task x) tsk).
            rewrite EXCHANGE /=; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
            rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
            apply leq_sum; move => j0 /andP [IN0 HP0].
            rewrite big_mkcond (big_rem (job_task j0)) /=;
                    first by rewrite HP0 andTb eq_refl; apply leq_addr.
              by apply in_arrivals_implies_arrived in IN0;
              apply H_all_jobs_from_taskset.
          }
          apply leq_sum_seq; intros tsk0 INtsk0 HP0.
          apply leq_trans with (
            task_cost tsk0 * num_arrivals_of_task job_task arr_seq tsk0 t (t + delta)).
          {
            rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
            rewrite -/l /workload_of_jobs.
            rewrite /is_job_of_task  muln1.
            apply leq_sum_seq; move => j0 IN0 /eqP EQ.
            rewrite -EQ.
            apply H_job_cost_le_task_cost.
              by apply in_arrivals_implies_arrived in IN0.
          }
          {
            rewrite leq_mul2l; apply/orP; right.
            rewrite -{2}[delta](addKn t).
            apply H_is_arrival_bound; [by done | by rewrite leq_addr].
          }
        Qed.

        Lemma total_workload_le_total_rbf'':
          total_workload t (t + delta) <= total_rbf delta.
        Proof.
          intros.
          rewrite /total_rbf 
                  /task_request_bound_function.
          rewrite /total_workload /workload_of_jobs.
          rewrite /arrivals_between.
          
          set l := jobs_arrived_between arr_seq t (t + delta).
          rewrite big_mkcond //=.

          
          apply leq_trans with
          (n := \sum_(tsk' <- ts)
                 (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
          {
            intros.
            have EXCHANGE := exchange_big_dep predT.
            rewrite EXCHANGE /=; last by done. 
            rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
            apply leq_sum; move => j0 /andP [IN0 HP0].
            rewrite big_mkcond (big_rem (job_task j0)) /=.
            rewrite eq_refl; apply leq_addr.
              by apply in_arrivals_implies_arrived in IN0;
              apply H_all_jobs_from_taskset.
          }
          apply leq_sum_seq; intros tsk0 INtsk0 HP0.
          apply leq_trans with (
            task_cost tsk0 * num_arrivals_of_task job_task arr_seq tsk0 t (t + delta)).
          {
            rewrite /num_arrivals_of_task -sum1_size big_distrr /= big_filter.
            rewrite -/l /workload_of_jobs.
            rewrite /is_job_of_task  muln1.
            apply leq_sum_seq; move => j0 IN0 /eqP EQ.
            rewrite -EQ.
            apply H_job_cost_le_task_cost.
              by apply in_arrivals_implies_arrived in IN0.
          }
          {
            rewrite leq_mul2l; apply/orP; right.
            rewrite -{2}[delta](addKn t).
            apply H_is_arrival_bound; [by done | by rewrite leq_addr].
          }
        Qed.  

      End WorkloadIsBoundedByRBF.

    End ProofWorkloadBound.
    
  End Lemmas.
  
End MaxArrivalsWorkloadBound.