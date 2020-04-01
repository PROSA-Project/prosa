Require Export prosa.util.all.
Require Export prosa.model.processor.platform_properties.
Require Export prosa.analysis.facts.behavior.service.

(** Throughout this file, we assume ideal uni-processor schedules. *)
Require Import prosa.model.processor.ideal.

(** Note: we do not re-export the basic definitions to avoid littering the global
   namespace with type class instances. *)

(** In this section we establish the classes to which an ideal schedule belongs. *)
Section ScheduleClass.

  Local Transparent service_in scheduled_in scheduled_on.
  (** Consider any job type and the ideal processor model. *)
  Context {Job: JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.  

  (** We note that the ideal processor model is indeed a uni-processor
     model. *)
  Lemma ideal_proc_model_is_a_uniprocessor_model:
    uniprocessor_model (processor_state Job).
  Proof.
    move=> j1 j2 sched t /existsP[[]/eqP E1] /existsP[[]/eqP E2].
    by move: E1 E2=>->[].
  Qed.

  (** We observe that the ideal processor model falls into the category
     of ideal-progress models, i.e., a scheduled job always receives
     service. *)
  Lemma ideal_proc_model_ensures_ideal_progress:
    ideal_progress_proc_model (processor_state Job).
  Proof.
    move=> j s /existsP[[]/eqP->]/=.
    by rewrite eqxx.
  Qed.

  (** The ideal processor model is a unit-service model. *)
  Lemma ideal_proc_model_provides_unit_service:
    unit_service_proc_model (processor_state Job).
  Proof.
    move=> j s.
    rewrite /service_in/=/nat_of_bool.
    by case:ifP.
  Qed.

  Lemma scheduled_in_def (j : Job) s :
    scheduled_in j s = (s == Some j).
  Proof.
    rewrite /scheduled_in/scheduled_on/=.
    case: existsP=>[[_->]//|].
    case: (s == Some j)=>//=[[]].
      by exists.
  Qed.

  Lemma scheduled_at_def sched (j : Job) t :
    scheduled_at sched j t = (sched t == Some j).
  Proof.
      by rewrite /scheduled_at scheduled_in_def.
  Qed.

  Lemma service_in_is_scheduled_in (j : Job) s :
    service_in j s = scheduled_in j s.
  Proof.
    by rewrite /service_in scheduled_in_def/=.
  Qed.

  Lemma service_at_is_scheduled_at sched (j : Job) t :
    service_at sched j t = scheduled_at sched j t.
  Proof.
      by rewrite /service_at service_in_is_scheduled_in.
  Qed.
    
  (** Next we prove a lemma which helps us to do a case analysis on
   the state of an ideal schedule. *)
  Lemma ideal_proc_model_sched_case_analysis:
    forall (sched : schedule (ideal.processor_state Job)) (t : instant),
      is_idle sched t \/ exists j, scheduled_at sched j t. 
  Proof.
    intros.
    unfold is_idle; simpl; destruct (sched t) eqn:EQ.
    - by right; exists s; auto; rewrite scheduled_at_def EQ.
    - by left; auto.
  Qed.
  
End ScheduleClass.

(** * Incremental Service in Ideal Schedule *)
(** In the following section we prove a few facts about service in ideal schedule. *)
(* Note that these lemmas can be generalized to an arbitrary scheduler. *)
Section IncrementalService.

  (** Consider any job type, ... *)
  Context {Job : JobType}.
  Context `{JobArrival Job}.
  Context `{JobCost Job}.

  (** ... any arrival sequence, ... *)
  Variable arr_seq : arrival_sequence Job.

  (** ... and any ideal uni-processor schedule of this arrival sequence. *)
  Variable sched : schedule (ideal.processor_state Job).  

  (** As a base case, we prove that if a job j receives service in
      some time interval <<[t1,t2)>>, then there exists a time instant t
      ∈ [t1,t2) such that j is scheduled at time t and t is the first
      instant where j receives service. *)
  Lemma positive_service_during:
    forall j t1 t2,
      0 < service_during sched j t1 t2 -> 
      exists t : nat, t1 <= t < t2 /\ scheduled_at sched j t /\ service_during sched j t1 t = 0.
  Proof.
    intros j t1 t2 SERV.
    have LE: t1 <= t2.
    { rewrite leqNgt; apply/negP; intros CONTR.
        by apply ltnW in CONTR;  move: SERV; rewrite /service_during big_geq.
    }
    destruct (scheduled_at sched j t1) eqn:SCHED.
    { exists t1; repeat split; try done.
      - apply/andP; split; first by done.
        rewrite ltnNge; apply/negP; intros CONTR.
          by move: SERV; rewrite/service_during big_geq.
      - by rewrite /service_during big_geq.                
    }  
    { apply negbT in SCHED.
      move: SERV; rewrite /service /service_during; move => /sum_seq_gt0P [t [IN SCHEDt]].
      rewrite lt0b in SCHEDt.
      rewrite mem_iota subnKC in IN; last by done.
      move: IN => /andP [IN1 IN2].
      move: (exists_first_intermediate_point
               ((fun t => scheduled_at sched j t)) t1 t IN1 SCHED) => A.
      feed A; first by rewrite scheduled_at_def/=.
      move: A => [x [/andP [T1 T4] [T2 T3]]].
      exists x; repeat split; try done.
      - apply/andP; split; first by apply ltnW.
          by apply leq_ltn_trans with t. 
      - apply/eqP; rewrite big_nat_cond big1 //.
        move => y /andP [T5 _].
          by apply/eqP; rewrite eqb0; specialize (T2 y); rewrite scheduled_at_def/= in T2; apply T2.
    }
  Qed.

  (** Next, we prove that if in some time interval <<[t1,t2)>> a job j
     receives k units of service, then there exists a time instant t ∈
     [t1,t2) such that j is scheduled at time t and service of job j
     within interval [t1,t) is equal to k. *)
  Lemma incremental_service_during:
    forall j t1 t2 k,
      service_during sched j t1 t2 > k ->
      exists t, t1 <= t < t2 /\ scheduled_at sched j t /\ service_during sched j t1 t = k.
  Proof.
    intros j t1 t2 k SERV.
    have LE: t1 <= t2.
    { rewrite leqNgt; apply/negP; intros CONTR.
        by apply ltnW in CONTR;  move: SERV; rewrite /service_during big_geq.
    }
    induction k; first by apply positive_service_during in SERV.
    feed IHk; first by apply ltn_trans with k.+1.
    move: IHk => [t [/andP [NEQ1 NEQ2] [SCHEDt SERVk]]].
    have SERVk1: service_during sched j t1 t.+1 = k.+1.
    { rewrite -(service_during_cat _ _ _ t); last by apply/andP; split.
      rewrite  SERVk -[X in _ = X]addn1; apply/eqP; rewrite eqn_add2l.
        by rewrite /service_during big_nat1 /service_at eqb1 -scheduled_at_def/=.  
    } 
    move: SERV; rewrite -(service_during_cat _ _ _ t.+1); last first.
    { by apply/andP; split; first apply leq_trans with t. }
    rewrite SERVk1 -addn1 leq_add2l; move => SERV.
    destruct (scheduled_at sched j t.+1) eqn:SCHED.
    - exists t.+1; repeat split; try done. apply/andP; split.
      + apply leq_trans with t; by done. 
      + rewrite ltnNge; apply/negP; intros CONTR.
          by move: SERV; rewrite /service_during big_geq.
    -  apply negbT in SCHED.
       move: SERV; rewrite /service /service_during; move => /sum_seq_gt0P [x [INx SCHEDx]].
       rewrite lt0b in SCHEDx.
       rewrite mem_iota subnKC in INx; last by done.
       move: INx => /andP [INx1 INx2].
       move: (exists_first_intermediate_point _ _ _ INx1 SCHED) => A.
       feed A; first by rewrite scheduled_at_def/=.
       move: A => [y [/andP [T1 T4] [T2 T3]]].
       exists y; repeat split; try done.
       + apply/andP; split.
         apply leq_trans with t; first by done. 
         apply ltnW, ltn_trans with t.+1; by done.
           by apply leq_ltn_trans with x. 
       + rewrite (@big_cat_nat _ _ _ t.+1) //=; [ | by apply leq_trans with t | by apply ltn_trans with t.+1].
         unfold service_during in SERVk1; rewrite SERVk1; apply/eqP.
         rewrite -{2}[k.+1]addn0 eqn_add2l.
         rewrite big_nat_cond big1 //; move => z /andP [H5 _].
           by apply/eqP; rewrite eqb0; specialize (T2 z); rewrite scheduled_at_def/= in T2; apply T2.
  Qed.

End IncrementalService.

(** * Automation *)
(** We add the above lemmas into a "Hint Database" basic_facts, so Coq 
    will be able to apply them automatically. *)
Hint Resolve ideal_proc_model_is_a_uniprocessor_model
     ideal_proc_model_ensures_ideal_progress
     ideal_proc_model_provides_unit_service : basic_facts.

(** We also provide tactics for case analysis on ideal processor state. *)

(** The first tactic generates two sub-goals: one with idle processor and 
    the other with processor executing a job named [JobName]. *)
Ltac ideal_proc_model_sched_case_analysis sched t JobName :=
  let Idle := fresh "Idle" in
  let Sched := fresh "Sched_" JobName in
  destruct (ideal_proc_model_sched_case_analysis sched t) as [Idle | [JobName Sched]].

(** The second tactic is similar to the first, but it additionally generates 
    two equalities: [sched t = None] and [sched t = Some j]. *)
Ltac ideal_proc_model_sched_case_analysis_eq sched t JobName :=
  let Idle := fresh "Idle" in
  let IdleEq := fresh "Eq" Idle in
  let Sched := fresh "Sched_" JobName in 
  let SchedEq := fresh "Eq" Sched in
  destruct (ideal_proc_model_sched_case_analysis sched t) as [Idle | [JobName Sched]];
  [move: (Idle) => /eqP IdleEq; rewrite ?IdleEq
  | move: (Sched); simpl; move => /eqP SchedEq; rewrite ?SchedEq].