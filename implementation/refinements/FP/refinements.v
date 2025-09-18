Require Export prosa.implementation.refinements.refinements.
Require Export prosa.implementation.refinements.FP.fast_search_space.
Require Export prosa.implementation.refinements.arrival_bound.


(** Throughout this file, we work with Prosa's fixed-priority policy implementation. *)
#[local] Existing Instance NumericFPAscending.

(** We begin by defining a generic version of the functions we seek to define. *)
Section Definitions.

  (** Consider a generic type T supporting basic arithmetic operations,
        neutral elements, and comparisons. *)
  Context `{T : Type}.
  Context `{!zero_of T, !one_of T, !sub_of T, !add_of T, !mul_of T,
            !div_of T, !mod_of T, !eq_of T, !leq_of T, !lt_of T}.
  Context `{!eq_of (seq T)}.
  Context {eq_of2 : eq_of (@task_T T)}.

  (** We define a generic version of higher-or-equal priority task, ... *)
  Definition hep_task_T tsk_o tsk := (task_priority_T tsk <= @task_priority_T T tsk_o)%C.

  (** ... of total request-bound function of higher-or-equal priority task, ...  *)
  Definition total_hep_rbf_T (ts : seq task_T) (tsk : task_T) (Δ : T) : T :=
    let hep_ts := filter (fun tsk' => hep_task_T tsk' tsk) ts in
    let work_ts := map (fun tsk' => task_rbf_T tsk' Δ) hep_ts in
    foldr +%C 0%C work_ts.

  (** ... an analogous version of [hep_task] in without symmetry, ... *)
  Definition ohep_task_T tsk_o tsk :=
    (hep_task_T tsk_o tsk) && (~~ (eq_of2 tsk_o tsk)%C).

  (** ... with a respective cumulative version. *)
  Definition total_ohep_rbf_T (ts : seq task_T) (tsk : task_T) (Δ : T) : T :=
    let hep_ts := filter (fun tsk' => ohep_task_T tsk' tsk) ts in
    let work_ts := map (fun tsk' => task_rbf_T tsk' Δ) hep_ts in
    foldr +%C 0%C work_ts.

  (** Next, we define a generic version of [check_point_FP], ... *)
  Definition check_point_FP_T (ts : seq task_T) (tsk : task_T) (R : T) (P : T * T) : bool :=
    (task_rbf_T tsk (P.1 + 1) + total_ohep_rbf_T ts tsk (P.1 + P.2)
     <= P.1 + P.2)%C && (P.2 <= R)%C.

  (** ... a generic version of [blocking_bound_NP], ... *)
  Definition blocking_bound_NP_T (ts : seq task_T) (tsk : task_T) :=
    let lp_ts := filter (fun tsk_o => ~~ hep_task_T tsk_o tsk) ts in
    let block_ts := map (fun tsk_o => task_cost_T tsk_o - 1)%C lp_ts in
    foldr maxn_T 0%C block_ts.

  (** ... and of [check_point_NP]. *)
  Definition check_point_NP_T (ts : seq task_T) (tsk : task_T) (R : T) (P : T * T) : bool :=
    (blocking_bound_NP_T ts tsk
     + (task_rbf_T tsk (P.1 + 1) - (task_cost_T tsk - 1))
     + total_ohep_rbf_T ts tsk (P.1 + P.2) <= P.1 + P.2)%C
    && (P.2 + (task_cost_T tsk - 1) <= R)%C.

End Definitions.

(** In this section, we introduce some functions operating on binary numbers. *)
Section DefinitionsN.

  (** We provide a definition of [iota], ... *)
  Definition iota_N (a Δ : N) := iota_T a Δ.

  (** ... of [search_space_emax_FP_h], ... *)
  Definition search_space_emax_FP_h_N (tsk : task_T) (l r : N) : seq N :=
    let h := get_horizon_of_task_T tsk in
    let offsets := map (N.mul h) (iota_N l r) in
    let emax_offsets := repeat_steps_with_offset_T tsk offsets in
    map predn_T emax_offsets.

  (** ... and of [search_space_emax_FP]. *)
  Definition search_space_emax_FP_N (tsk : task_T) (L : N) :=
    let h := get_horizon_of_task_T tsk in
    search_space_emax_FP_h_N tsk 0 (((L %/ h)+1))%C.

End DefinitionsN.

(** ** Refinements *)

(** We now establish the desired refinements. *)

(** First, we prove a refinement for the [search_space_emax_h] function. *)
Local Instance refine_search_space_emax_h :
  refines (Rtask ==> Rnat ==> Rnat ==> list_R Rnat)%rel
          search_space_emax_FP_h
          search_space_emax_FP_h_N.
Proof.
  rewrite refinesE => tsk tsk' Rtsk l l' Rl r r' Rr.
  apply refinesP; unfold search_space_emax_FP_h, search_space_emax_FP_h_N.
  by refines_apply; refines_abstr.
Qed.

(** Next, we prove a refinement for the [search_space_emax_FP] function. *)
Global Instance refine_search_space_emax :
  forall tsk,
    refines (Rnat ==> list_R Rnat)%rel
            (search_space_emax_FP (taskT_to_task tsk))
            (search_space_emax_FP_N tsk).
Proof.
  intros.
  rewrite refinesE => δ δ' Rδ.
  unfold search_space_emax_FP, search_space_emax_FP_N.
  apply refinesP; rewrite -addn1.
  by refines_apply; rewrite refinesE; unfold Rtask, fun_hrel.
Qed.

(** Next, we prove a refinement for the [hep_task] function. *)
Global Instance refine_hep_task :
  refines ( Rtask ==> Rtask ==> bool_R )%rel hep_task hep_task_T.
Proof.
  apply refines_abstr2.
  rewrite /hep_task /hep_task_T /NumericFPAscending
          /numeric_fixed_priority.task_priority /TaskPriority.
  move=> tsk1 tsk1' Rtsk1 tsk2 tsk2' Rtsk2.
  by refines_apply.
Qed.

(** Next, we prove a refinement for the [total_hep_rbf] function. *)
Global Instance refine_total_hep_rbf :
  refines ( list_R Rtask ==> Rtask ==> Rnat ==> Rnat )%rel total_hep_rbf total_hep_rbf_T.
Proof.
  apply refines_abstr => ts ts' Rts.
  apply refines_abstr => tsk tsk' Rtsk.
  apply refines_abstr => Δ Δ' RΔ.
  rewrite /total_hep_rbf /total_hep_request_bound_function_FP /total_hep_rbf_T.
  eapply refine_foldr.
  - by apply Rts.
  - by apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
  - by apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
Qed.

(** Next, we prove a special-case refinement for the [total_hep_rbf] function
    when applied to a refined task set and a refined task. This special case
    is required to guide the typeclass engine. *)
Global Instance refine_total_hep_rbf' :
  forall ts tsk,
    refines (Rnat ==> Rnat)%rel
            (total_hep_rbf (map taskT_to_task ts) (taskT_to_task tsk))
            (total_hep_rbf_T ts tsk) | 0.
Proof.
  move=> ts tsk; rewrite refinesE => δ δ' Rδ.
  move: refine_task_set' => RTS.
  rewrite refinesE in RTS.
  specialize (RTS ts ts (unifyxx _)); simpl in RTS.
  apply refinesP.
  move: refine_total_hep_rbf => EQ.
  refines_apply.
  move: refine_task' => Rtsk.
  rewrite refinesE; rewrite refinesE in Rtsk.
  by apply Rtsk.
Qed.

(** Next, we provide equality comparisons between different pairs of objects
    manipulated in Poet's certificates. *)
Global Instance eq_listN : eq_of (seq N) := fun x y => x == y.
Global Instance eq_listNN : eq_of (seq (prod N N)) := fun x y => x == y.
Global Instance eq_NlistNN : eq_of (prod N (seq (prod N N))) := fun x y => x == y.
Global Instance eq_taskab : eq_of (@task_arrivals_bound_T N) := taskab_eqdef_T.
Global Instance eq_task : eq_of (@task_T N) := task_eqdef_T.

(** Next, we prove a refinement for the [task_eqdef] function. *)
Global Instance refine_task_eqdef :
  refines (Rtask ==> Rtask ==> bool_R)%rel task_eqdef task_eqdef_T.
Proof.
  apply refines_abstr2.
  intros a a' Ra b b' Rb.
  unfold task_eqdef, task_eqdef_T.
  by rewrite refinesE; repeat apply andb_R; apply refinesP; refines_apply.
Qed.

(** Next, we prove a refinement for the [ohep_task] function. *)
Global Instance refine_ohep_task :
  refines ( Rtask ==> Rtask ==> bool_R )%rel ohep_task ohep_task_T.
Proof.
  apply refines_abstr2.
  rewrite /ohep_task /ohep_task_T /NumericFPAscending
          /numeric_fixed_priority.task_priority /TaskPriority.
  move=> tsk1 tsk1' Rtsk1 tsk2 tsk2' Rtsk2.
  by refines_apply.
Qed.

(** Next, we prove a refinement for the [total_ohep_rbf] function. *)
Global Instance refine_total_ohep_rbf :
  refines ( list_R Rtask ==> Rtask ==> Rnat ==> Rnat )%rel total_ohep_rbf total_ohep_rbf_T.
Proof.
  apply refines_abstr => ts ts' Rts.
  apply refines_abstr => tsk tsk' Rtsk.
  apply refines_abstr => Δ Δ' RΔ.
  rewrite /total_hep_rbf /total_hep_request_bound_function_FP.
  eapply refine_foldr.
  - by apply Rts.
  - by apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
  - by unfold ohep_task_T; apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
Qed.

(** Next, we prove a refinement for the [check_point_FP] function. *)
Global Instance refine_check_point :
  refines (list_R Rtask ==> Rtask ==> Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
          check_point_FP check_point_FP_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk l l' Rl p p' Rp.
  by unfold check_point_FP, check_point_FP_T; apply andb_R; apply refinesP; tc.
Qed.

(** Next, we prove a special-case refinement for the [check_point_FP] function
    when applied to a refined task set and a refined task. This special case
    is required to guide the typeclass engine. *)
Global Instance refine_check_point' :
  forall ts tsk,
    refines (Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
            (check_point_FP (map taskT_to_task ts) (taskT_to_task tsk))
            (check_point_FP_T ts tsk) | 0.
Proof.
  intros ts tsk; rewrite refinesE => l l' Rl p p' Rp.
  unfold check_point_FP, check_point_FP_T; apply andb_R; apply refinesP; tc.
  move: refine_task' => RT.
  move: refine_task_set' => RTS.
  rewrite refinesE in RT; rewrite refinesE in RTS.
  by refines_apply; rewrite refinesE; [apply RT | apply RTS | apply RT].
Qed.

(** Next, we prove a refinement for the [blocking_bound_NP] function. *)
Global Instance refine_blocking_bound :
  refines ( list_R Rtask ==> Rtask ==> Rnat )%rel blocking_bound_NP blocking_bound_NP_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk.
  unfold blocking_bound, blocking_bound_NP_T.
  apply refinesP; eapply refine_foldr_max.
  - by rewrite refinesE; apply Rts.
  - by apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
  - by apply refines_abstr => tsk1 tsk1' Rtsk1; tc.
Qed.

(** Next, we prove a special-case refinement for the [blocking_bound_NP] function
    when applied to a refined task set and a refined task. This special case
    is required to guide the typeclass engine. *)
Global Instance refine_blocking_bound' :
  forall ts tsk,
    refines ( Rnat )%rel
            (blocking_bound_NP (map taskT_to_task ts) (taskT_to_task tsk))
            (blocking_bound_NP_T ts tsk) | 0.
Proof.
  intros ts tsk; rewrite refinesE.
  move: refine_task' => RT.
  move: refine_task_set' => RTS.
  rewrite refinesE in RT; rewrite refinesE in RTS.
  by apply refinesP; refines_apply; (rewrite refinesE; (apply RT || apply RTS)).
Qed.

(** Next, we prove a refinement for the [check_point_NP] function. *)
Global Instance refine_check_point_NP :
  refines (list_R Rtask ==> Rtask ==> Rnat ==> prod_R Rnat Rnat ==> bool_R)%rel
          check_point_NP check_point_NP_T.
Proof.
  rewrite refinesE => ts ts' Rts tsk tsk' Rtsk l l' Rl p p' Rp.
  by unfold check_point_NP, check_point_NP_T; apply andb_R; apply refinesP; tc.
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
  unfold check_point_NP, check_point_NP_T; apply andb_R; apply refinesP; refines_apply.
  all: try by (rewrite refinesE; (apply RT || apply RTS)).
Qed.
