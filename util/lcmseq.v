From mathcomp Require Export ssreflect seq div ssrbool ssrnat eqtype ssrfun.
Require Export prosa.util.tactics.

(** A function to calculate the least common multiple
    of all integers in a sequence [xs], denoted by [lcml xs]. *)
Definition lcml (xs : seq nat) : nat := foldr lcmn 1 xs.

(** First we show that [x] divides [lcml (x :: xs)] for any [x] and [xs]. *)
Lemma int_divides_lcm_in_seq :
  forall (x : nat) (xs : seq nat), x %| lcml (x :: xs).
Proof.
  move=> x xs; induction xs.
  - by apply dvdn_lcml.
  - rewrite /lcml -cat1s foldr_cat /foldr.
    by apply dvdn_lcml.
Qed.

(** Similarly, [lcml xs] divides [lcml (x :: xs)] for any [x] and [xs]. *)
Lemma lcm_seq_divides_lcm_super :
  forall (x : nat) (xs : seq nat),
    lcml xs %| lcml (x :: xs).
Proof.
  move=> x xs; induction xs; first by auto.
  rewrite /lcml -cat1s foldr_cat /foldr.
  by apply dvdn_lcmr.
Qed.

(** Given a sequence [xs], any integer [x \in xs] divides [lcml xs]. *)
Lemma lcm_seq_is_mult_of_all_ints :
  forall (x : nat) (xs : seq nat), x \in xs -> x %| lcml xs.
Proof.
  intros x xs IN; apply/dvdnP.
  induction xs as [ | z sq IH_DIV]; first by done.
  rewrite in_cons in IN.
  move : IN => /orP [/eqP EQ | IN].
  - apply /dvdnP.
    rewrite EQ /lcml.
    by apply int_divides_lcm_in_seq.
  - move : (IH_DIV IN) => [k EQ].
    exists ((foldr lcmn 1 (z :: sq)) %/ (foldr lcmn 1 sq) * k).
    rewrite -mulnA -EQ divnK /lcml //.
    by apply lcm_seq_divides_lcm_super.
Qed.

(** The LCM of all elements in a sequence with only positive elements is positive. *)
Lemma all_pos_implies_lcml_pos :
  forall (xs : seq nat),
    (forall x, x \in xs -> x > 0) ->
    lcml xs > 0.
Proof.
  elim=> [//|x xs IHxs] POS.
  rewrite /lcml -cat1s //= lcmn_gt0.
  apply/andP; split => //.
  - by apply POS; rewrite in_cons eq_refl.
  - apply: IHxs; intros b B_IN.
    by apply POS; rewrite in_cons; apply /orP; right => //.
Qed.
