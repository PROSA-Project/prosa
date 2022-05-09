Require Export prosa.implementation.facts.maximal_arrival_sequence.
Require Export prosa.implementation.definitions.task.

(** * Job Constructor *)

(** In this file, we define a job-generation function to use in pair with a
    concrete arrival sequence. These facts sit at the basis of POET's
    assumption-less certificates, used to prove the absence of contradicting
    hypotheses in abstract RTA. *)

(** The generated jobs to belong to the concrete task type. *)
Definition Task := [eqType of concrete_task].
Definition Job := [eqType of concrete_job].


(** We first define a job-generation function that produces one concrete job of
    the given task, with the given job ID, arriving at the given time ... *)
Definition generate_job_at tsk t id : Job :=
  {| task.job_id := id
  ;  task.job_arrival := t
  ;  task.job_cost := task_cost tsk
  ;  task.job_deadline := t + task_deadline tsk
  ;  task.job_task := tsk |}.

(** ... and then generalize the above function to an arbitrary number of
    jobs. *)
Definition generate_jobs_at tsk n t := map (generate_job_at tsk t) (iota 0 n).
