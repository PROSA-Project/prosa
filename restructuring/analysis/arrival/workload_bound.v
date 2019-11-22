Require Import rt.util.sum.
Require Export rt.restructuring.behavior.all.
Require Import rt.restructuring.model.task.
Require Import rt.restructuring.model.priority.classes.
Require Import rt.restructuring.model.aggregate.task_arrivals.
Require Import rt.restructuring.model.arrival.arrival_curves.
Require Import rt.restructuring.analysis.basic_facts.workload.
Require Import rt.restructuring.analysis.basic_facts.ideal_schedule.
Require Import rt.restructuring.analysis.basic_facts.arrivals.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Task Workload Bounded by Arrival Curves *)
Section TaskWorkloadBoundedByArrivalCurves.

  (** Consider any type of tasks ... *)
  Context {Task : TaskType}.
  Context `{TaskCost Task}.

  (**  ... and any type of jobs associated with these tasks. *)
  Context {Job : JobType}.
  Context `{JobTask Job Task}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.
  
  (** Consider any arrival sequence with consistent, non-duplicate arrivals... *)
  Variable arr_seq : arrival_sequence Job.
  Hypothesis H_arrival_times_are_consistent : consistent_arrival_times arr_seq.
  Hypothesis H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq.

  (** ... and any ideal uniprocessor schedule of this arrival sequence.*)
  Variable sched : schedule (ideal.processor_state Job).
  Hypothesis H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq.

  (** Consider an FP policy that indicates a higher-or-equal priority relation. *)
  Variable higher_eq_priority : FP_policy Task.
  Let jlfp_higher_eq_priority := FP_to_JLFP Job Task.

  (** For simplicity, let's define some local names. *)
  Let arrivals_between := arrivals_between arr_seq.
  
  (** We define the notion of request bound function. *)
  Section RequestBoundFunction.
    
    (** Let MaxArrivals denote any function that takes a task and an interval length
       and returns the associated number of job arrivals of the task. *) 
    Context `{MaxArrivals Task}.
    
    (** In this section, we define a bound for the workload of a single task
       under uniprocessor FP scheduling. *)
    Section SingleTask.

      (** Consider any task tsk that is to be scheduled in an interval of length delta. *)
      Variable tsk : Task.
      Variable delta : duration.

      (** We define the following workload bound for the task. *)
      Definition task_request_bound_function := task_cost tsk * max_arrivals tsk delta.

    End SingleTask.

    (** In this section, we define a bound for the workload of multiple tasks. *)
    Section AllTasks.

      (** Consider a task set ts... *)
      Variable ts : list Task.

      (** ...and let tsk be any task in task set. *)
      Variable tsk : Task.
      
      (** Let delta be the length of the interval of interest. *)
      Variable delta : duration.
      
      (** Recall the definition of higher-or-equal-priority task and
         the per-task workload bound for FP scheduling. *)
      Let is_hep_task tsk_other := higher_eq_priority tsk_other tsk.
      Let is_other_hep_task tsk_other := higher_eq_priority tsk_other tsk && (tsk_other != tsk).

      (** Using the sum of individual workload bounds, we define the following bound
         for the total workload of tasks in any interval of length delta. *)
      Definition total_request_bound_function :=
        \sum_(tsk <- ts) task_request_bound_function tsk delta.
      
      (** Similarly, we define the following bound for the total workload of tasks of 
         higher-or-equal priority (with respect to tsk) in any interval of length delta. *)
      Definition total_hep_request_bound_function_FP :=
        \sum_(tsk_other <- ts | is_hep_task tsk_other)
         task_request_bound_function tsk_other delta.
      
      (** We also define a bound for the total workload of higher-or-equal 
         priority tasks other than tsk in any interval of length delta. *)
      Definition total_ohep_request_bound_function_FP :=
        \sum_(tsk_other <- ts | is_other_hep_task tsk_other)
         task_request_bound_function tsk_other delta.
      
    End AllTasks.

  End RequestBoundFunction.

  (** In this section we prove some lemmas about request bound functions. *)
  Section ProofWorkloadBound.

    (** Consider a task set ts... *)
    Variable ts : list Task.

    (** ...and let tsk be any task in ts. *)
    Variable tsk : Task.
    Hypothesis H_tsk_in_ts : tsk \in ts.

    (** Assume that the job costs are no larger than the task costs. *)
    Hypothesis H_job_cost_le_task_cost :
      cost_of_jobs_from_arrival_sequence_le_task_cost arr_seq.

    (** Next, we assume that all jobs come from the task set. *)
    Hypothesis H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts.
      
    (** Let max_arrivals be any arrival bound for taskset ts. *)
    Context `{MaxArrivals Task}.
    Hypothesis H_is_arrival_bound : taskset_respects_max_arrivals arr_seq ts. 
    
    (** Let's define some local names for clarity. *)
    Let task_rbf := task_request_bound_function tsk.
    Let total_rbf := total_request_bound_function ts.
    Let total_hep_rbf := total_hep_request_bound_function_FP ts tsk.
    Let total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk.

    (** Next, we consider any job j of tsk. *)
    Variable j : Job.
    Hypothesis H_j_arrives : arrives_in arr_seq j.
    Hypothesis H_job_of_tsk : job_task j = tsk.
    
    (** Next, we say that two jobs j1 and j2 are in relation other_higher_eq_priority, iff 
       j1 has higher or equal priority than j2 and is produced by a different task. *)
    Let other_higher_eq_priority j1 j2 := jlfp_higher_eq_priority j1 j2 && (~~ same_task j1 j2).

    (** Next, we recall the notions of total workload of jobs... *)
    Let total_workload t1 t2 := workload_of_jobs predT (arrivals_between t1 t2).
    
    (** ...notions of workload of higher or equal priority jobs... *)
    Let total_hep_workload t1 t2 :=
      workload_of_jobs (fun j_other => jlfp_higher_eq_priority j_other j) (arrivals_between t1 t2).
    
    (** ... workload of other higher or equal priority jobs... *)
    Let total_ohep_workload t1 t2 :=
      workload_of_jobs (fun j_other => other_higher_eq_priority j_other j) (arrivals_between t1 t2).

    (** ... and the workload of jobs of the same task as job j. *)
    Let task_workload t1 t2 :=
      workload_of_jobs (job_of_task tsk) (arrivals_between t1 t2).
    
    (** In this section we prove that the workload of any jobs is 
       no larger than the request bound function. *) 
    Section WorkloadIsBoundedByRBF.

      (** Consider any time t and any interval of length delta. *)
      Variable t : instant.
      Variable delta : instant.

      (** First, we show that workload of task tsk is bounded by 
         the number of arrivals of the task times the cost of the task. *)
      Lemma task_workload_le_num_of_arrivals_times_cost:
        task_workload t (t + delta)
        <= task_cost tsk * number_of_task_arrivals arr_seq tsk t (t + delta).
      Proof.
        rewrite // /number_of_task_arrivals -sum1_size big_distrr /= big_filter.
        rewrite /task_workload_between /workload.task_workload_between /task_workload /workload_of_jobs.
        rewrite /same_task -H_job_of_tsk muln1.
        apply leq_sum_seq; move => j0 IN0 /eqP EQ.
        rewrite -EQ; apply in_arrivals_implies_arrived in IN0; auto.
          by apply H_job_cost_le_task_cost.
      Qed.
      
      (** As a corollary, we prove that workload of task is 
         no larger the than task request bound function. *)
      Corollary task_workload_le_task_rbf:
        task_workload t (t + delta) <= task_rbf delta.
      Proof.    
        apply leq_trans with
            (task_cost tsk *  number_of_task_arrivals arr_seq tsk t (t + delta));
          first by apply task_workload_le_num_of_arrivals_times_cost.
        rewrite leq_mul2l; apply/orP; right.
        rewrite -{2}[delta](addKn t).
          by apply H_is_arrival_bound; last rewrite leq_addr.
      Qed.

      (** Next, we prove that total workload of other tasks with
         higher-or-equal priority is no larger than the total
         request bound function. *)
      Lemma total_workload_le_total_rbf:
        total_ohep_workload t (t + delta) <= total_ohep_rbf delta.
      Proof.        
        set l := arrivals_between t (t + delta).
        set hep := higher_eq_priority.        
        apply leq_trans with
            (\sum_(tsk' <- ts | hep tsk' tsk && (tsk' != tsk))
              (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
        { intros.
          rewrite /total_ohep_workload /workload_of_jobs /other_higher_eq_priority.
          rewrite /jlfp_higher_eq_priority /FP_to_JLFP /same_task H_job_of_tsk. 
          have EXCHANGE := exchange_big_dep (fun x => hep (job_task x) tsk && (job_task x != tsk)).
          rewrite EXCHANGE /=; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
          rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
          apply leq_sum; move => j0 /andP [IN0 HP0].
          rewrite big_mkcond (big_rem (job_task j0)) /=; first by rewrite HP0 andTb eq_refl; apply leq_addr.
            by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset.
        }
        apply leq_sum_seq; intros tsk0 INtsk0 HP0.
        apply leq_trans with
            (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + delta))).
        { rewrite -sum1_size big_distrr /= big_filter.
          rewrite /workload_of_jobs.
          rewrite  muln1 /l /arrivals_between /arrival_sequence.arrivals_between. 
          apply leq_sum_seq; move => j0 IN0 /eqP EQ.
            by rewrite -EQ; apply H_job_cost_le_task_cost; apply in_arrivals_implies_arrived in IN0.
        }
        { rewrite leq_mul2l; apply/orP; right.
          rewrite -{2}[delta](addKn t).
            by apply H_is_arrival_bound; last rewrite leq_addr.
        }
      Qed.

      (** Next, we prove that total workload of tasks with higher-or-equal 
         priority is no larger than the total request bound function. *)
      Lemma total_workload_le_total_rbf':
        total_hep_workload t (t + delta) <= total_hep_rbf delta.
      Proof.
        set l := arrivals_between t (t + delta).
        set hep := higher_eq_priority.
        apply leq_trans with
            (n := \sum_(tsk' <- ts | hep tsk' tsk)
                   (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
        { rewrite /total_hep_workload /jlfp_higher_eq_priority /FP_to_JLFP H_job_of_tsk. 
          have EXCHANGE := exchange_big_dep (fun x => hep (job_task x) tsk).
          rewrite EXCHANGE /=; clear EXCHANGE; last by move => tsk0 j0 HEP /eqP JOB0; rewrite JOB0.
          rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
          apply leq_sum; move => j0 /andP [IN0 HP0].
          rewrite big_mkcond (big_rem (job_task j0)) /=; first by rewrite HP0 andTb eq_refl; apply leq_addr.
            by apply in_arrivals_implies_arrived in IN0; apply H_all_jobs_from_taskset.
        }
        apply leq_sum_seq; intros tsk0 INtsk0 HP0.
        apply leq_trans with
            (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + delta))).
        { rewrite -sum1_size big_distrr /= big_filter.
          rewrite -/l /workload_of_jobs.
          rewrite muln1.
          apply leq_sum_seq; move => j0 IN0 /eqP EQ.
          rewrite -EQ.
          apply H_job_cost_le_task_cost.
            by apply in_arrivals_implies_arrived in IN0.
        }
        { rewrite leq_mul2l; apply/orP; right.
          rewrite -{2}[delta](addKn t).
            by apply H_is_arrival_bound; last rewrite leq_addr.
        }
      Qed.
      
      (** Next, we prove that total workload of tasks is 
         no larger than the total request bound function. *)
      Lemma total_workload_le_total_rbf'':
        total_workload t (t + delta) <= total_rbf delta.
      Proof.
        set l := arrivals_between t (t + delta).
        apply leq_trans with
            (n := \sum_(tsk' <- ts)
                   (\sum_(j0 <- l | job_task j0 == tsk') job_cost j0)).
        { rewrite /total_workload.
          have EXCHANGE := exchange_big_dep predT.
          rewrite EXCHANGE /=; clear EXCHANGE; last by done. 
          rewrite /workload_of_jobs -/l big_seq_cond [X in _ <= X]big_seq_cond.
          apply leq_sum; move => j0 /andP [IN0 HP0].
          rewrite big_mkcond (big_rem (job_task j0)) /=.
          rewrite eq_refl; apply leq_addr.
            by apply in_arrivals_implies_arrived in IN0;
              apply H_all_jobs_from_taskset.
        }
        apply leq_sum_seq; intros tsk0 INtsk0 HP0.
        apply leq_trans with
            (task_cost tsk0 * size (task_arrivals_between arr_seq tsk0 t (t + delta))).
        { rewrite -sum1_size big_distrr /= big_filter.
          rewrite -/l /workload_of_jobs.
          rewrite muln1.
          apply leq_sum_seq; move => j0 IN0 /eqP EQ.
          rewrite -EQ.
          apply H_job_cost_le_task_cost.
            by apply in_arrivals_implies_arrived in IN0.
        }
        { rewrite leq_mul2l; apply/orP; right.
          rewrite -{2}[delta](addKn t).
            by apply H_is_arrival_bound; last rewrite leq_addr.
        }
      Qed.  

    End WorkloadIsBoundedByRBF.

  End ProofWorkloadBound.
  
End TaskWorkloadBoundedByArrivalCurves.