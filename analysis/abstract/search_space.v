Require Import prosa.util.epsilon.
Require Import prosa.util.tactics.
Require Import prosa.model.task.concept.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq path fintype bigop.

(** * Reduction of the search space for Abstract RTA *)
(** In this file, we prove that in order to calculate the worst-case response time 
    it is sufficient to consider only values of [A] that lie in the search space defined below. *)  

Section AbstractRTAReduction. 

  (** The response-time analysis we are presenting in this series of documents is based on searching 
     over all possible values of [A], the relative arrival time of the job respective to the beginning 
     of the busy interval. However, to obtain a practically useful response-time bound, we need to 
     constrain the search space of values of [A]. In this section, we define an approach to 
     reduce the search space. *)
  
  Context {Task : TaskType}.
  
  (** First, we provide a constructive notion of equivalent functions. *)
  Section EquivalentFunctions.
    
    (** Consider an arbitrary type [T]... *)
    Context {T : eqType}.

    (**  ...and two function from [nat] to [T]. *)
    Variables f1 f2 : nat -> T.

    (** Let [B] be an arbitrary constant. *) 
    Variable B : nat.
    
    (** Then we say that [f1] and [f2] are equivalent at values less than [B] iff
       for any natural number [x] less than [B] [f1 x] is equal to [f2 x].  *)
    Definition are_equivalent_at_values_less_than :=
      forall x, x < B -> f1 x = f2 x.

    (** And vice versa, we say that [f1] and [f2] are not equivalent at values 
       less than [B] iff there exists a natural number [x] less than [B] such
       that [f1 x] is not equal to [f2 x].  *)
    Definition are_not_equivalent_at_values_less_than :=
      exists x, x < B /\ f1 x <> f2 x.

  End EquivalentFunctions. 

  (** Let [tsk] be any task that is to be analyzed *)
  Variable tsk : Task.
  
  (** To ensure that the analysis procedure terminates, we assume an upper bound [B] on 
     the values of [A] that must be checked. The existence of [B] follows from the assumption 
     that the system is not overloaded (i.e., it has bounded utilization). *)
  Variable B : duration.

  (** Instead of searching for the maximum interference of each individual job, we 
     assume a per-task interference bound function [IBF(tsk, A, x)] that is parameterized 
     by the relative arrival time [A] of a potential job (see abstract_RTA.definitions.v file). *)
  Variable interference_bound_function : Task -> duration -> duration -> duration.

  (** Recall the definition of [ε], which defines the neighborhood of a point in the timeline.
     Note that [ε = 1] under discrete time. *)
  (** To ensure that the search converges more quickly, we only check values of [A] in the interval 
     <<[0, B)>> for which the interference bound function changes, i.e., every point [x] in which 
     [interference_bound_function (A - ε, x)] is not equal to [interference_bound_function (A, x)]. *)
  Definition is_in_search_space A :=
    A = 0 \/
    0 < A < B /\ are_not_equivalent_at_values_less_than
                  (interference_bound_function tsk (A - ε)) (interference_bound_function tsk A) B.
  
  (** In this section we prove that for every [A] there exists a smaller [A_sp] 
     in the search space such that [interference_bound_function(A_sp,x)] is 
     equal to [interference_bound_function(A, x)]. *)
  Section ExistenceOfRepresentative.

    (** Let [A] be any constant less than [B]. *) 
    Variable A : duration.
    Hypothesis H_A_less_than_B : A < B.
    
    (** We prove that there exists a constant [A_sp] such that:
       (a) [A_sp] is no greater than [A], (b) [interference_bound_function(A_sp, x)] is 
       equal to [interference_bound_function(A, x)] and (c) [A_sp] is in the search space.
       In other words, either [A] is already inside the search space, or we can go 
       to the "left" until we reach [A_sp], which will be inside the search space. *)
    Lemma representative_exists:
      exists A_sp, 
        A_sp <= A /\
        are_equivalent_at_values_less_than (interference_bound_function tsk A)
                                           (interference_bound_function tsk A_sp) B /\
        is_in_search_space A_sp.
    Proof.
      induction A as [|n].
      - exists 0; repeat split.
          by rewrite /is_in_search_space; left.
      - have ALT:
          all (fun t => interference_bound_function tsk n t == interference_bound_function tsk n.+1 t) (iota 0 B)
          \/ has (fun t => interference_bound_function tsk n t != interference_bound_function tsk n.+1 t) (iota 0 B).
        { apply/orP.
          rewrite -[_ || _]Bool.negb_involutive Bool.negb_orb.
          apply/negP; intros CONTR.
          move: CONTR => /andP [NALL /negP NHAS]; apply: NHAS.
            by rewrite -has_predC /predC in NALL.
        }
        feed IHn; first by apply ltn_trans with n.+1. 
        move: IHn => [ASP [NEQ [EQ SP]]].
        move: ALT => [/allP ALT| /hasP ALT].
        { exists ASP; repeat split; try done.
          { by apply leq_trans with n. }
          { intros x LT.
            move: (ALT x) => T. feed T; first by rewrite mem_iota; apply/andP; split. 
            move: T => /eqP T.
              by rewrite -T EQ.
          }
        }
        { exists n.+1; repeat split; try done.
          rewrite /is_in_search_space; right.
          split; first by  apply/andP; split.
          move: ALT => [y IN N].
          exists y.
          move: IN; rewrite mem_iota add0n. move => /andP [_ LT]. 
          split; first by done.
          rewrite subn1 -pred_Sn.
          intros CONTR; move: N => /negP N; apply: N.
            by rewrite CONTR.
        }
    Qed.

  End ExistenceOfRepresentative.

  (** In this section we prove that any solution of the response-time recurrence for
     a given point [A_sp] in the search space also gives a solution for any point 
     A that shares the same interference bound. *)
  Section FixpointSolutionForAnotherA.

    (** Suppose [A_sp + F_sp] is a "small" solution (i.e. less than [B]) of the response-time recurrence. *)
    Variables A_sp F_sp : duration.
    Hypothesis H_less_than : A_sp + F_sp < B.
    Hypothesis H_fixpoint : A_sp + F_sp = interference_bound_function tsk A_sp (A_sp + F_sp).

    (** Next, let [A] be any point such that: (a) [A_sp <= A <= A_sp + F_sp] and 
       (b) [interference_bound_function(A, x)] is equal to 
       [interference_bound_function(A_sp, x)] for all [x] less than [B]. *)
    Variable A : duration.
    Hypothesis H_bounds_for_A : A_sp <= A <= A_sp + F_sp.
    Hypothesis H_equivalent :
      are_equivalent_at_values_less_than
        (interference_bound_function tsk A)
        (interference_bound_function tsk A_sp) B.

    (** We prove that there exists a constant [F] such that [A + F] is equal to [A_sp + F_sp]
       and [A + F] is a solution for the response-time recurrence for [A]. *)
    Lemma solution_for_A_exists:
      exists F,
        A_sp + F_sp = A + F /\
        F <= F_sp /\
        A + F = interference_bound_function tsk A (A + F).
    Proof.  
      move: H_bounds_for_A => /andP [NEQ1 NEQ2].
      set (X := A_sp + F_sp) in *.
      exists (X - A); split; last split.
      - by rewrite subnKC.
      - by rewrite leq_subLR /X leq_add2r.
      - by rewrite subnKC // H_equivalent.
    Qed.

  End FixpointSolutionForAnotherA.
  
End AbstractRTAReduction. 