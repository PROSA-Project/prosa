Require Import prosa.classic.util.all.
Require Import prosa.classic.model.suspension.
Require Import prosa.classic.model.schedule.uni.susp.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq bigop fintype.

(* In this file, we take any predicate that defines whether a job
   is suspended at time t and build a table of suspension durations
   that is valid up to time t. *)
Module SuspensionTableConstruction.

  Import ScheduleWithSuspensions Suspension.

  Section BuildingSuspensionTable.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (** Basic Setup & Setting *)
    
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.
        
    (* ...and any schedule of this arrival sequence... *)
    Variable sched: schedule Job.

    (* ...in which jobs must arrive to execute. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.

    (* Recall the instant following the last execution of a job, which
       indicates the start of the latest suspension interval. *)
    Let start_of_latest_suspension :=
      time_after_last_execution job_arrival sched.

    (* For simplicity, let's also define some local names. *)
    Let job_completed_by := completed_by job_cost sched.

    (** Construction of Suspension Table *)

    (* We are going to construct a suspension table that is valid up to time t_max. *)
    Variable t_max: time.

    (* First, consider any predicate that indicates whether a job is suspended at time t. *)
    Variable job_suspended_at: Job -> time -> bool.
    
    (* Assume that this predicate only holds for jobs that have arrived... *)
    Hypothesis H_arrived:
      forall j t,
        t < t_max ->
        job_suspended_at j t ->
        has_arrived job_arrival j t.

    (* ...and that have not yet completed. *)
    Hypothesis H_not_completed:
      forall j t,
        t < t_max ->
        job_suspended_at j t ->
        ~~ job_completed_by j t.

    (* Assume that this predicate divides the timeline into continuous
       suspension intervals, for any given amount of received service. *)
    Hypothesis H_continuous_suspension:
      forall j t t_susp,
        t < t_max ->
        job_suspended_at j t ->
        start_of_latest_suspension j t <= t_susp < t ->
        job_suspended_at j t_susp.

    (* Then, we can construct a suspension table for the given suspension
       predicate as follows. *)
    Definition build_suspension_duration (j: Job) (s: time) :=
        \sum_(0 <= t < t_max | service sched j t == s) job_suspended_at j t.
    
    (* In order to prove that the suspension table matches the given predicate,
       let's first prove some helper lemmas. *)
    Section HelperLemmas.

      (* First, we show that for any job j suspended at time t, the cumulative suspension
         time before the beginning of the suspension is zero. *)
      Lemma not_suspended_before_suspension_start:
        forall j t,
          t < t_max ->
          job_suspended_at j t ->
          let susp_start := start_of_latest_suspension j t in
          let S := service sched j in
            \sum_(0 <= i < susp_start | S i == S susp_start) job_suspended_at j i = 0.
      Proof.
        rename H_arrived into ARR, H_not_completed into COMPLETED,
               H_continuous_suspension into CONT.
        intros j t LTmax SUSPt X1 X2; rewrite /X1 /X2; clear X1 X2.
        set ex := start_of_latest_suspension.
        set S := service sched.
        rewrite big_nat_cond big1 ?add0n //.
        move => i /= /andP [LTex /eqP SAME].
        apply/eqP; rewrite eqb0; apply/negP; intro SUSPi.
        suff BUG: S j i != S j (ex j t) by rewrite SAME eq_refl in BUG.
        rewrite neq_ltn; apply/orP; left.
        rewrite /S/ex (same_service_since_last_execution job_arrival) //.
        eapply less_service_before_start_of_suspension; last by apply LTex.
        apply ARR; last by done.
        apply ltn_trans with (n := ex j t); first by done.
        apply leq_ltn_trans with (n := t); last by done.
        by apply last_execution_bounded_by_identity, ARR.
      Qed.

      (* Next, we prove that after time t_max, no job suspends according to the table. *)
      Lemma suspension_duration_no_suspension_after_t_max:
        forall j t,
          has_arrived job_arrival j t ->
          t_max <= t ->
          ~~ suspended_at job_arrival job_cost build_suspension_duration sched j t.
      Proof.
        have ZERO := not_suspended_before_suspension_start.
        rename H_arrived into ARR.
        intros j t ARRt GEmax.
        rewrite /suspended_at negb_and; apply/orP; right.
        rewrite negb_and -leqNgt; apply/orP; right.
        rewrite /suspension_duration /build_suspension_duration.
        set ex := _ job_arrival _.
        set S := service sched.
        set susp_at := job_suspended_at.
        case (ltnP (ex j t) t_max) => [LT | GE].
        {
          apply leq_trans with (n := t_max); last by done.
          rewrite big_mkcond /=.
          rewrite -> big_cat_nat with (n := ex j t); [simpl | by done | by apply ltnW].
          rewrite big_nat_cond big1 ?add0n.
          {
            apply leq_trans with (n := ex j t + \sum_(ex j t <= i < t_max) 1);
              last by simpl_sum_const; rewrite subnKC // ltnW.
            by rewrite leq_add2l; apply leq_sum; intros i _; case: ifP => //_; apply leq_b1.
          }
          move => /= i /andP [LTex _]; case: ifP => /eqP SERV; last by done.
          apply/eqP; rewrite eqb0; apply/negP; intro SUSPi.
          suff BUG: S j i != S j (ex j t) by rewrite SERV eq_refl in BUG.
          rewrite neq_ltn; apply/orP; left.
          rewrite /S/ex same_service_since_last_execution //.
          eapply less_service_before_start_of_suspension; last by apply LTex.
          by apply ARR; first by apply:(ltn_trans LTex).
        }
        {
          rewrite big_nat_cond big1 ?addn0;
            first by apply last_execution_bounded_by_identity.
          move => /= i /andP [LTmax /eqP SERV].
          apply/eqP; rewrite eqb0; apply/negP; intro SUSPi.
          suff BUG: S j i != S j (ex j t) by rewrite SERV eq_refl in BUG.
          rewrite neq_ltn; apply/orP; left.
          rewrite /S/ex same_service_since_last_execution //.
          eapply less_service_before_start_of_suspension; first by apply ARR.
          by apply: (leq_trans LTmax); apply GE.
        }
      Qed.

    End HelperLemmas.
    
    (* Using the lemmas above, we prove that up to time t_max, the constructed suspension
       table matches the given suspension predicate. *)
    Lemma suspension_duration_matches_predicate_up_to_t_max:
      forall j t,
        t < t_max ->
        job_suspended_at j t =
        suspended_at job_arrival job_cost build_suspension_duration sched j t.
    Proof.
      have ZERO := not_suspended_before_suspension_start.
      rename H_arrived into ARR, H_not_completed into COMPLETED,
             H_continuous_suspension into CONT.
      intros j t LEmax.
      apply/idP/idP.
      {
        intros SUSPt.
        set ex := time_after_last_execution job_arrival sched.
        set S := service sched.
        set susp_at := job_suspended_at.
        have LEt: ex j t <= t.
          by apply last_execution_bounded_by_identity, ARR.
        apply/andP; split; first by apply COMPLETED.
        apply/andP; split; first by done.
        rewrite /suspension_duration /build_suspension_duration.
        rewrite -/ex -/S -/susp_at.
        apply leq_trans with (n := ex j t + \sum_(ex j t <= t0 < t.+1) 1);
          first by simpl_sum_const; rewrite subnKC // ltnW // ltnS.
        rewrite leq_add2l.
        rewrite -> big_cat_nat with (m := 0) (n := ex j t); rewrite //=;
          last by apply leq_trans with (n := t); last by apply ltnW.
        rewrite ZERO // add0n.
        apply leq_trans with (n := \sum_(ex j t<= i <t.+1|S j i==S j (ex j t)) susp_at j i);
          last by rewrite big_mkcond [X in _ <= X]big_mkcond /= extend_sum.
        rewrite [X in _ <= X]big_mkcond /=.
        apply leq_sum_nat; move => i /andP [GE LT] _.
        have SAMEserv: S j i == S j (ex j t).
        {
          rewrite ltnS in LT.
          rewrite eqn_leq; apply/andP; split; last by apply extend_sum.
          by rewrite /S/ex same_service_since_last_execution ?extend_sum.
        }
        rewrite SAMEserv lt0n eqb0 negbK.
        rewrite ltnS leq_eqVlt in LT.
        move: LT => /orP [/eqP EQ | LT]; subst; first by done.
        by apply CONT with (t := t); try (apply/andP; split).
      }
      {
        move => /andP [NOTCOMP /andP [GE LT]].
        rewrite /suspension_duration /build_suspension_duration in LT.
        set S := service sched in LT.
        set susp_at := job_suspended_at in LT *.
        set ex := _ job_arrival _ in GE LT.
        rewrite -> big_cat_nat with (m := 0) (n := ex j t) in LT; rewrite //= in LT;
          last by apply leq_trans with (n := t); last by apply ltnW.
        rewrite big_nat_cond big1 ?add0n in LT; last first.
        {
          move => i /= /andP [LTex /eqP SAME].
          apply/eqP; rewrite eqb0; apply/negP; intro SUSPi.
          suff BUG: S j i != S j (ex j t) by rewrite SAME eq_refl in BUG.
          rewrite neq_ltn; apply/orP; left.
          rewrite /S/ex same_service_since_last_execution //.
          eapply less_service_before_start_of_suspension; last by apply LTex.
          by apply ARR; first by apply:(ltn_trans LTex); apply:(leq_ltn_trans _ LEmax).
        }
        case (boolP ([exists t0:'I_t_max,(S j t0==S j (ex j t))&&susp_at j t0]));last first.
        {
          rewrite negb_exists; move => /forallP ALL.
          rewrite big_nat_cond big1 in LT; first by rewrite addn0 ltnNge GE in LT.
          move => i /andP [/andP [_ LTmax] EQ].
          specialize (ALL (Ordinal LTmax)).
          by rewrite EQ /= in ALL; apply/eqP; rewrite eqb0.
        }
        move => /existsP [t0 /andP [/eqP EQ SUSP0]].
        have MAX := @arg_maxP _ t0 (fun x=>(S j x == S j (ex j t)) && susp_at j x) id. 
        feed MAX; simpl in MAX; first by rewrite EQ eq_refl SUSP0.
        move: MAX => [m /andP [/eqP EQserv SUSPm] ALL]; clear EQ SUSP0 t0.
        case (ltnP t m) => [LTm | GEm].
        {
          apply CONT with (t := m); try done; apply/andP; split; last by done.
          rewrite /start_of_latest_suspension.
          rewrite (same_service_implies_same_last_execution _ _ _ _ t); first by done.
          rewrite -/S EQserv /S /ex /start_of_latest_suspension.
          by rewrite same_service_since_last_execution.
        }
        rewrite leq_eqVlt in GEm; move: GEm => /orP [/eqP EQm | GTm]; subst; first by done.
        apply contraT; intro NOTSUSP.
        set SUM := (X in _ < _ + X) in LT.
        suff BUG: t >= ex j t + SUM by rewrite leqNgt LT in BUG.
        rewrite /SUM in LT *; clear SUM LT.
        apply leq_trans with (n := ex j t + (t - ex j t)); last by rewrite subnKC.
        rewrite leq_add2l.
        rewrite -> big_cat_nat with (n := t); rewrite //=; last by apply ltnW.
        rewrite [X in _ + X <= _]big_nat_cond [X in _ + X <= _]big1 ?addn0.
        {
          apply leq_trans with (n := \sum_(ex j t <= i < t) 1); last by simpl_sum_const.
          by rewrite big_mkcond; apply leq_sum; intros i _; case: ifP => // _; apply leq_b1.
        }
        move => i /andP [/andP [GEi LTi] /eqP SERVi].
        apply/eqP; rewrite eqb0; apply/negP; intro SUSPi.
        specialize (ALL (Ordinal LTi)); rewrite /= in ALL.
        feed ALL; first by rewrite SERVi eq_refl SUSPi.
        suff BUG: m >= t by rewrite leqNgt GTm in BUG.
        by apply: (leq_trans GEi).
      }
    Qed.

  End BuildingSuspensionTable.

End SuspensionTableConstruction.