Require Export prosa.implementation.refinements.refinements.
Require Export prosa.implementation.refinements.task.
Require Export prosa.implementation.refinements.EDF.fast_search_space.
Require Export prosa.implementation.refinements.arrival_bound.

(** We begin by defining a generic version of the functions we seek to define. *)
Section Definitions.

  (** Consider a generic type T supporting basic arithmetic operations,
        neutral elements, and comparisons. *)
  Context {T : Type}.
  Context `{!zero_of T, !one_of T, !sub_of T, !add_of T, !mul_of T,
            !div_of T, !mod_of T, !eq_of T, !leq_of T, !lt_of T}.
  Context `{!eq_of (seq T)}.
  Context {eq_of2 : eq_of (@task_T T)}.

  (** We define a generic version of total request-bound function of
      higher-or-equal priority task, ... *)
  Definition total_rbf_T (ts : seq task_T) (Δ : T) : T :=
    let work_ts := map (fun tsk' => task_rbf_T tsk' Δ) ts in
    foldr +%C 0%C work_ts.

  (** ... of bound on total higher-or-equal priority workload, ...  *)
  Definition bound_on_total_hep_workload_T (ts : seq task_T) (tsk : task_T) (A Δ : T) : T :=
    let o_ts := filter (fun tsk_o => ~~ (eq_of2 tsk_o tsk)) ts in
    let o_work := map (fun tsk_o => task_rbf_T tsk_o (minn_T ((A + 1) + task_deadline_T tsk - task_deadline_T tsk_o) Δ))%C o_ts in
    foldr +%C 0%C o_work.

  (** Next, we define a generic version of [check_point_FP], ... *)
  Definition check_point_FP_T (ts : seq task_T) (tsk : task_T) (R : T) (P : T * T) : bool :=
    (task_rbf_T tsk (P.1 + 1) + bound_on_total_hep_workload_T ts tsk P.1 (P.1 + P.2) <= P.1 + P.2)%C
    && (P.2 <= R)%C.

  (** ... a generic version of [blocking_bound_NP], ... *)
  Definition blocking_bound_NP_T (ts : seq task_T) (tsk : task_T) A :=
    let blocking_relevant tsk_o := (0 < ConcreteMaxArrivals_T tsk_o 1)%C  && (0 < task_cost_T tsk_o)%C in
    let ts_lp := filter (fun tsk_o => (blocking_relevant tsk_o)
                                    && (@task_deadline_T T tsk + A < @task_deadline_T T tsk_o))%C ts in
    let ts_block := map (fun tsk_o => task_cost_T tsk_o - 1)%C ts_lp in
    foldr maxn_T 0%C ts_block.

  (** ... of [check_point_NP], ... *)
  Definition check_point_NP_T (ts : seq task_T) (tsk : task_T) (R : T) (P : T * T) : bool :=
    (blocking_bound_NP_T ts tsk P.1
     + (task_rbf_T tsk (P.1 + 1) - (task_cost_T tsk - 1))
     + bound_on_total_hep_workload_T ts tsk P.1 (P.1 + P.2) <= P.1 + P.2)%C
    && (P.2 + (task_cost_T tsk - 1) <= R)%C.

  (** ... of [valid_arrivals]. *)
  Definition valid_arrivals_T (tsk : task_T) : bool :=
    match @task_arrival_T T tsk with
    | Periodic_T p => (1 <= p)%C
    | Sporadic_T m => (1 <= m)%C
    | ArrivalPrefix_T emax_vec => valid_extrapolated_arrival_curve_T emax_vec
    end.

End Definitions.

(** In the following, we introduce some functions operating on binary numbers. *)

(** We provide a definition of [iota], ... *)
Definition iota_N (a Δ : N) := iota_T a Δ.

(** ... of [task_search_space_emax_EDF_h], ... *)
Definition task_search_space_emax_EDF_h_N (tsk tsko : task_T) (l r : N) : seq N :=
  let h := get_horizon_of_task_T tsko in
  let offsets := map (N.mul h) (iota_N l r) in
  let emax_offsets := repeat_steps_with_offset_T tsko offsets in
  let emax_edf_offsets :=
      shift_points_neg_T
        (shift_points_pos_T emax_offsets (task_deadline_T tsko))
        (task_deadline_T tsk) in
  map predn_T emax_edf_offsets.

(** ... of [task_search_space_emax_EDF], ... *)
Definition task_search_space_emax_EDF_N (tsk tsko : task_T)  (L : N) :=
  let h := get_horizon_of_task_T tsko in
  task_search_space_emax_EDF_h_N
    tsk tsko 0
    (((L + (task_deadline_T tsk - task_deadline_T tsko)) %/ h) + 1)%C.

(** ... and of [search_space_emax_EDF_N]. *)
Definition search_space_emax_EDF_N (ts : seq task_T) (tsk : task_T) (L : N) :=
  let points := map (fun tsko => task_search_space_emax_EDF_N tsk tsko L) ts in
  flatten points.

(** ** Refinements *)

(** We now establish the desired refinements. *)

(** First, we prove a refinement for the [task_search_space_emax_EDF_h] function. *)
Local Instance refine_task_search_space_emax_EDF_h :
  refines (Rtask ==> Rtask ==> Rnat ==> Rnat ==> list_R Rnat)%rel
          task_search_space_emax_EDF_h
          task_search_space_emax_EDF_h_N.
Proof.
  rewrite refinesE => tsk tsk' Rtsk tsko tsko' Rtsko l l' Rl r r' Rr.
  apply refinesP; unfold task_search_space_emax_EDF_h, task_search_space_emax_EDF_h_N.
  by refines_apply; refines_abstr.
Qed.

(** Next, we prove a refinement for the [task_search_space_emax_EDF] function. *)
Global Instance refine_task_search_space_emax_EDF :
  forall tsk tsko,
    refines (Rnat ==> list_R Rnat)%rel
            (task_search_space_emax_EDF (taskT_to_task tsk) (taskT_to_task tsko))
            (task_search_space_emax_EDF_N tsk tsko).
Proof.
  intros.
  rewrite refinesE => δ δ' Rδ.
  unfold task_search_space_emax_EDF, task_search_space_emax_EDF_N.
  apply refinesP; rewrite -addn1.
  refines_apply.
  all: by rewrite refinesE; unfold Rtask, fun_hrel.
Qed.

(** Next, we prove a refinement for the [search_space_emax_EDF] function. *)
Global Instance refine_search_space_emax_EDF :
  forall ts tsk,
    refines (Rnat ==> list_R Rnat)%rel
            (search_space_emax_EDF (map taskT_to_task ts) (taskT_to_task tsk))
            (search_space_emax_EDF_N ts tsk).
Proof.
  move=> ts tsk.
  unfold search_space_emax_EDF, search_space_emax_EDF_N.
  rewrite refinesE => L L' RL; apply refinesP.
  have F: forall xs f, \cat_(x <- xs) f x = flatten (map f xs).
  { clear=> T T0; elim=> [|x xs IHxs] f.
    - by rewrite big_nil.
    - by rewrite big_cons //= IHxs. }
  rewrite F; clear F.
  refines_apply.
  Unshelve.
  5: exact (Rtask ==> list_R Rnat)%rel.
  4: exact (list_R Rtask).
  - rewrite refinesE => f f' Rf xs xs' Rxs; apply refinesP.
    by eapply refine_map; [rewrite refinesE; exact Rxs | rewrite refinesE ].
  - move: refine_task_search_space_emax_EDF=> R; rewrite refinesE in R.
    by rewrite refinesE => tsko tsko' Rtsko; rewrite -Rtsko; apply R.
  - move: refine_task_set' => RTS.
    rewrite refinesE; rewrite refinesE in RTS.
    by apply RTS; apply unifyxx.
Qed.

(** Next, we prove a refinement for the [total_request_bound_function] function. *)
Local Instance refine_total_rbf :
  refines (list_R Rtask ==> Rnat ==> Rnat)%rel total_request_bound_function total_rbf_T.
Proof.
  apply refines_abstr2;
    rewrite /total_request_bound_function /total_rbf_T /total_request_bound_function
            /concept.task_cost /TaskCost /max_arrivals /MaxArrivals => t t' Rt y y' Ry.
  eapply refine_uncond_foldr; first exact Rt.
  by rewrite refinesE => tsko tsko' Rtsko; apply refinesP; refines_apply.
Qed.

(** Next, we prove a special-case refinement for the [total_request_bound_function] function
    when applied to a refined task set and a refined task. This special case
    is required to guide the typeclass engine. *)
Global Instance refine_total_rbf' :
  forall ts,
    refines (Rnat ==> Rnat)%rel
            (total_request_bound_function (map taskT_to_task ts))
            (total_rbf_T ts) | 0.
Proof.
  move=> ts; rewrite refinesE => δ δ' Rδ.
  move: refine_task_set' => RTS.
  rewrite refinesE in RTS.
  specialize (RTS ts ts (unifyxx _)); simpl in RTS.
  apply refinesP.
  move: (refine_total_rbf) => EQ.
  rewrite refinesE in EQ.
  erewrite <-EQ; [ | eassumption | eassumption].
  set (x := total_rbf_T _ _).
  by rewrite refinesE.
Qed.

(** Next, we provide equality comparisons between different pairs of objects
    manipulated in Poet's certificates. *)
Global Instance eq_listN : eq_of (seq N) := fun x y => x == y.
Global Instance eq_NlistNN : eq_of (prod N (seq (prod N N))) := fun x y => x == y.
Global Instance eq_taskab : eq_of (@task_arrivals_bound_T N) := taskab_eqdef_T.
Global Instance eq_task : eq_of (@task_T N) := task_eqdef_T.

(** Next, we prove a refinement for the [task_eqdef] function. *)
Local Instance refine_task_eqdef :
  refines (Rtask ==> Rtask ==> bool_R)%rel task_eqdef task_eqdef_T.
Proof.
  apply refines_abstr2.
  intros a a' Ra b b' Rb.
  unfold task_eqdef, task_eqdef_T.
  by rewrite refinesE; repeat apply andb_R; apply refinesP; refines_apply.
Qed.

(** Next, we prove a refinement for the [bound_on_total_hep_workload] function. *)
Global Instance refine_bound_on_total_hep_workload :
  refines (list_R Rtask ==> Rtask ==> Rnat ==> Rnat ==> Rnat)%rel
          bound_on_total_hep_workload bound_on_total_hep_workload_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk a a' Ra δ δ' Rδ.
  unfold bound_on_total_hep_workload, bound_on_total_hep_workload_T.
  apply refinesP.
  eapply refine_foldr; rewrite refinesE; first by apply Rts.
  all: by move=> tsko tsko' Rtsko; apply refinesP; refines_apply.
Qed.

(** Next, we prove a refinement for the [check_point_FP] function. *)
Global Instance refine_check_point_FP :
  refines (list_R Rtask ==> Rtask ==> Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
          check_point_FP check_point_FP_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk l l' Rl p p' Rp.
  unfold check_point_FP, check_point_FP_T.
  by apply andb_R; apply refinesP; tc.
Qed.

(** Next, we prove a special-case refinement for the [check_point_FP] function
    when applied to a refined task set and a refined task. This special case
    is required to guide the typeclass engine. *)
Global Instance refine_check_point_FP' :
  forall ts tsk,
    refines (Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
            (check_point_FP (map taskT_to_task ts) (taskT_to_task tsk))
            (check_point_FP_T ts tsk) | 0.
Proof.
  intros ts tsk; rewrite refinesE => l l' Rl p p' Rp.
  unfold check_point_NP, check_point_NP_T; apply andb_R; apply refinesP; tc.
  move: refine_task' => RT.
  move: refine_task_set' => RTS.
  rewrite refinesE in RT; rewrite refinesE in RTS.
  by refines_apply; rewrite refinesE; [apply RT | apply RTS | apply RT].
Qed.

(** Next, we prove a refinement for the [blocking_bound_NP] function. *)
Global Instance refine_blocking_bound :
  refines (list_R Rtask ==> Rtask ==> Rnat ==> Rnat)%rel blocking_bound_NP blocking_bound_NP_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk.
  unfold blocking_bound_NP, blocking_bound_NP_T, blocking_relevant.
  intros A A' RA; apply refinesP; eapply refine_foldr_max.
  - by rewrite refinesE map_id; apply Rts.
  - by apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
  - rewrite refinesE => tsk1 tsk1' Rtsk1.
    apply andb_R; first apply andb_R.
    + apply refine_ltn; first by done.
      by apply refinesP; rewrite /max_arrivals; refines_apply; apply refine_ConcreteMaxArrivals.
    + by apply refine_ltn; [done | apply refinesP; refines_apply].
    + move: refine_task_deadline => Ra.
      rewrite refinesE in Ra; specialize (Ra _ _ Rtsk1).
      move: refine_task_deadline => Rb.
      rewrite refinesE in Rb; specialize (Rb _ _ Rtsk).
      inversion Ra; inversion Rb.
      set (a := @task_deadline_T N tsk') in *.
      set (b := @task_deadline_T N tsk1') in *.
      by apply refine_ltn; [apply refinesP; refines_apply | done].
Qed.

(** Next, we prove a refinement for the [check_point_NP] function. *)
Global Instance refine_check_point_NP :
  refines (list_R Rtask ==> Rtask ==> Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
          check_point_NP check_point_NP_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk l l' Rl p p' Rp.
  unfold check_point_NP, check_point_NP_T.
  by apply andb_R; apply refinesP; tc.
Qed.

(** Finally, we prove a special-case refinement for the [check_point_NP] function
    when applied to a refined task set and a refined task. This special case
    is required to guide the typeclass engine. *)
Global Instance refine_check_point_NP' :
  forall ts tsk,
    refines (Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
            (check_point_NP (map taskT_to_task ts) (taskT_to_task tsk))
            (check_point_NP_T ts tsk) | 0.
Proof.
  intros ts tsk; rewrite refinesE => l l' Rl p p' Rp.
  move: refine_task' => RT.
  move: refine_task_set' => RTS.
  rewrite refinesE in RT; rewrite refinesE in RTS.
  unfold check_point_NP, check_point_NP_T.
  by apply andb_R; apply refinesP;refines_apply;rewrite refinesE;(apply RT || apply RTS).
Qed.
