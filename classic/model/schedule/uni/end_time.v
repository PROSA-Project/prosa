Require Import Arith Nat. 
Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task 
               prosa.classic.model.arrival.basic.job 
               prosa.classic.model.schedule.uni.schedule
               prosa.classic.model.schedule.uni.response_time.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Set Bullet Behavior "Strict Subproofs".

Module end_time.
  Import UniprocessorSchedule Job ResponseTime.

  Section Task.
    Context {task: eqType}.
    Variable task_cost: task -> time.
    Variable task_period: task -> time.
    Variable task_deadline: task -> time.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> task.

    (* instant option, to be used in end_time_option *)
    Inductive diagnosis_option : Set :=
      | OK      : instant -> diagnosis_option
      | Failure : instant -> diagnosis_option.

    Section Job_end_time_Def.

      (* Jobs will be scheduled on an uniprocessor *)
      Variable sched: schedule Job.

      (* Consider any job *)
      Variable job:Job.

      (* Recall the definition of scheduled_at for testing wether this job can 
        be scheduled at time t *)
      Let job_scheduled_at t:= scheduled_at sched job t = true. 

      (* We define the function calculating the job's end time.
         It takes three arguments:
         t : job arrival [instant]
         c : job cost [duration]
         wf: an extra parameter that allows to realize a well-founded fixpoint
             with the type [nat]. It is supposed big enough to return the actual end time.
             Otherwise (i.e., it reaches 0), the function returns Failure t *)
      Fixpoint end_time_option (t:instant) (c:duration) (wf:nat):=
        match c with
        | 0   =>  OK t
        | S c'=> match wf with
              | 0    => Failure t
              | S wf'=> if scheduled_at sched job t then end_time_option  (S t) c' wf'
                            else end_time_option  (S t) c wf'
              end
        end.

      (* We define an end time predicate with three arguments:
         the job arrival [instant], the job cost [duration] and 
         the job end time [instant]. Its three constructors 
         correspond to the cases:
         - cost = 0 and job has ended
         - cost > 0 and job cannot be scheduled at instant t
         - cost > 0 and job can be scheduled at instant t
      *)
      Inductive end_time_predicate : instant-> duration->instant->Prop:=
        |C0_: forall t, end_time_predicate t 0 t

        |S_C_not_sched: forall t c e,  
          ~job_scheduled_at  t->
          end_time_predicate  (S t) (S c) e->
          end_time_predicate  t (S c) e

        |S_C_sched: forall t c e,
          job_scheduled_at t->
          end_time_predicate (S t)  c e-> 
          end_time_predicate  t (S c) e.

      (* The predicate completes_at specifies the instant a job ends
          according to its arrival and cost *)
      Definition completes_at (t:instant):=
        end_time_predicate (job_arrival job) (job_cost job) t.

    End Job_end_time_Def.

    Section Lemmas.

      (* Consider any job *)
      Variable job:Job.

      (* ... and and uniprocessor schedule this job*)
      Variable sched: schedule Job.

      (* ... where jobs do not execute before their arrival times nor after completion *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute job_arrival sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      Hypothesis H_valid_job:
      valid_realtime_job job_cost job_deadline job.

      (* Recall the function end_time_option*)
      Let job_end_time_function:= end_time_option sched job.

      (* Recall the end time predicate*)
      Let job_end_time_p:= end_time_predicate sched job.

      (* Recall the definition of completes_at*)
      Let job_completes_at := completes_at sched job.

      (* Recall the definition of scheduled_at for testing wether this job can 
        be scheduled at time t.*)
      Let job_scheduled_at t:= scheduled_at sched job t = true. 

      (* Then, the job_end_time_function (if it terminates successfully) returns
         the same result as the job_end_time_p predicate *)
      (* function -> predicate *)
      Theorem end_time_function_predicat_equivalence:
        forall e wf t c,
          job_end_time_function t c wf = OK e ->
          job_end_time_p t c e.
      Proof. 
        induction wf as [| wf' IHwf']; intros t c; simpl.
        -  destruct c; intros H; inversion H .  
           apply C0_.
        -  intros IHSwf. case Hcases:(scheduled_at sched job t); destruct c.
          + inversion IHSwf. apply C0_.
          + rewrite Hcases in IHSwf. apply IHwf' in IHSwf. apply S_C_sched with (c:=c)(e:=e). 
            apply Hcases. apply IHSwf.
          + inversion IHSwf. apply C0_.
          + rewrite Hcases in IHSwf. apply IHwf' in IHSwf. apply S_C_not_sched with (c:=c)(e:=e). 
            * rewrite Hcases. done.
            * apply IHSwf.
      Qed.

      (* The end time given by the predicate job_end_time_p  is the same as
         the result returned by the function job_end_time_function (provided
         wf is large enough) *)
      Theorem end_time_predicat_function_equivalence:
        forall t c e ,
          job_end_time_p t c e ->
          exists wf, job_end_time_function t c wf = OK e.
      Proof.
        intros.
        induction H as [t|t c e Hcase1 Hpre [wf Hwf] |t c e Hcase2 Hpre [wf Hwf]].
        - exists 1. done.
        - exists (1+wf).
          case Csa:(scheduled_at sched job t).
          + done.
          + simpl. rewrite Csa. apply Hwf.
        - exists (1+wf). simpl. 
          rewrite Hcase2. apply Hwf.
      Qed.

      (* If we consider a time t where the job is not scheduled, then 
         the end_time_predicate returns the same end time starting from t or t+1 *)
      Lemma end_time_predicate_not_sched:
        forall t c e,
          ~(job_scheduled_at t) ->
          end_time_predicate sched job t c.+1 e ->
          end_time_predicate sched job t.+1 c.+1 e.
      Proof.
        intros* Hcase1 Hpre.
        induction t as [| t' IHt']; 
        inversion Hpre; try apply H2; done. 
      Qed.

      (* If we consider a time t where the job is scheduled, then the end_time_predicate 
         returns the same end time starting from t with a cost c+1 than from t+1 with a cost c*)
      Lemma end_time_predicate_sched:
        forall t c e,
          job_scheduled_at t ->
          end_time_predicate sched job t c.+1 e ->
          end_time_predicate sched job t.+1 c e.
      Proof.
        intros* Hcase2 Hpre.
        induction t as [| t' IHt']; 
        inversion Hpre; try apply H2; done. 
      Qed.

      (* Assume that the job end time is job_end *)
      Variable job_end: instant.

      (* Recall the definition of completed_by defined in
        model/schedule/uni/schedule.v *)
      Let job_completed_by:=
        completed_by job_cost sched.

      (* Recall the definition of service_during defined in
        model/schedule/uni/schedule.v *)
      Let job_service_during:=
        service_during sched job.

      (* then the job arrival is less than or equal to job end time *)
      Lemma arrival_le_end:
         forall t c e, job_end_time_p t c e -> t <= e.
      Proof.
        intros* G.
        induction G as [t|t c e Hcase1 Hpre |t c e Hcase2 Hpre]; ssromega.
      Qed.

      (* the sum of job arrival and job cost is less than or equal to 
        job end time*)
      Lemma arrival_add_cost_le_end:
        forall t c e,
          job_end_time_p t c e ->
          t+c<=e.
      Proof.
        intros* h1.
        induction h1 as [t|t c e Hcase1 Hpre |t c e Hcase2 Hpre]; ssromega.
      Qed.

      (* The servive received between the job arrival
         and the job end is equal to the job cost*)
      Lemma service_eq_cost_at_end_time:
        job_completes_at job_end ->
        job_service_during (job_arrival job) job_end = job_cost job.
      Proof.
        intros job_cmplted.
        induction job_cmplted as [t|t c e Hcase1 Hpre |t c e Hcase2 Hpre];
        unfold job_service_during, service_during in *.
        - by rewrite big_geq.
        - apply arrival_le_end in Hpre.
          rewrite big_ltn // IHHpre /service_at.
          case cases:(scheduled_at sched job t); try easy; done.
        - apply arrival_le_end in Hpre. 
          rewrite big_ltn // IHHpre /service_at. 
          rewrite Hcase2 //. 
      Qed.

      (* A job is completed by job end time*)
      Lemma completed_by_end_time:
        job_completes_at job_end ->
        job_completed_by job job_end.
      Proof.
        intro job_cmplted.
        unfold job_completed_by, completed_by, service, service_during. 
        rewrite (ignore_service_before_arrival job_arrival sched ) //. 
        - apply service_eq_cost_at_end_time in job_cmplted.
            by rewrite -job_cmplted. 
        - by apply arrival_le_end in job_cmplted.
      Qed.

      (* The job end time is positive *)
      Corollary end_time_positive:
        job_completes_at job_end -> job_end > 0.
      Proof.
        intro h1. 
        assert (H_slot: job_cost job > 0) by (apply H_valid_job).
        apply completed_by_end_time in h1.
        unfold job_completed_by, completed_by, service, service_during in h1.
        destruct job_end; trivial. 
        rewrite big_geq // in h1. 
        ssromega.
      Qed.

      (* The service received between job arrival and the previous instant
         of job end time is exactly job cost-1*)
      Lemma job_uncompletes_at_end_time_sub_1:
        job_completes_at job_end ->
        job_service_during (job_arrival job) (job_end .-1) = (job_cost job) .-1.
      Proof.
        intros job_cmplted.
        induction job_cmplted as [t|t c e Hcase1 Hpre |t c e Hcase2 Hpre];
        unfold job_service_during, service_during in*.
        - apply big_geq, leq_pred. 
        - apply arrival_add_cost_le_end, leq_sub2r with (p:=1) in Hpre.
          rewrite subn1 addnS //= addSn subn1 in Hpre.
          apply leq_ltn_trans with (m:=t) in Hpre; try (apply leq_addr).
          rewrite big_ltn // IHHpre /service_at /service_during.
          case C:(scheduled_at sched job t);done.  
        - destruct c. 
          + inversion Hpre. apply big_geq. ssromega.
          + apply arrival_add_cost_le_end, leq_sub2r with (p:=1) in Hpre.
            rewrite subn1 addnS //= addSn subn1 in Hpre.
            apply leq_ltn_trans with (m:=t) in Hpre; try (apply leq_addr).
            rewrite big_ltn // /service_at / service_during IHHpre Hcase2 //.
      Qed.

      (* At any instant from the job arrival and before the job end time,
         job cannot be finished; the service received is always less than job cost*)
      Lemma job_uncompleted_before_end_time:
        job_completes_at job_end ->
        forall t', job_arrival job <= t' /\ t'<= job_end.-1 -> 
           job_service_during (job_arrival job) t' < job_cost job.
      Proof.
        intros job_cmplted t' [ht1 ht2].
        assert (H_slot: job_cost job > 0) by (apply H_valid_job).
        apply leq_ltn_trans with (n:= (job_cost job).-1); last ssromega.
        rewrite -job_uncompletes_at_end_time_sub_1 // /job_service_during /service_during.
        assert (H_lt: exists delta, t' + delta = job_end.-1).
        - move/leP:ht2 => ht2.
          apply Nat.le_exists_sub in ht2.
          destruct ht2 as [p [ht21 ht22]]. exists p. ssromega.
        - destruct H_lt as [delta ht']. rewrite -ht'.
          replace (\sum_(job_arrival job <= t < t' + delta) service_at sched job t)
          with    (addn_monoid(\big[addn_monoid/0]_(job_arrival job <= i < t') service_at sched job i)
                  (\big[addn_monoid/0]_(t'  <= i < t'+delta) service_at sched job i)); simpl; try ssromega.
          symmetry. apply big_cat_nat; ssromega.
      Qed.

    End Lemmas.

  End Task.

End end_time.