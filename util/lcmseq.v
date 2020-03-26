From mathcomp Require Export ssreflect seq div ssrbool ssrnat eqtype ssrfun.

(** A function to calculate the least common multiple 
    of all integers in a sequence [xs], denoted by [lcml xs]  **)
Definition lcml (xs : seq nat) : nat := foldr lcmn 1 xs.

(** Any integer [a] that is contained in the sequence [xs] divides [lcml xs]. **)
Lemma int_divides_lcm_in_seq : 
  forall (a : nat) (xs : seq nat), a %| lcml (a :: xs).
Proof.
  intros.
  rewrite /lcml.
  induction xs.
  - rewrite /foldr.
    now apply dvdn_lcml.
  - rewrite -cat1s.
    rewrite foldr_cat /foldr.
    by apply dvdn_lcml.
Qed.

(** Also, [lcml xs1] divides [lcml xs2] if [xs2] contains one extra element as compared to [xs1]. *)
Lemma lcm_seq_divides_lcm_super : 
  forall (x : nat) (xs : seq nat), 
  lcml xs %| lcml (x :: xs).
Proof.
  intros.
  rewrite /lcml.
  induction xs; first by auto.
  rewrite -cat1s foldr_cat /foldr.
  by apply dvdn_lcmr.
Qed.

(** All integers in a sequence [xs] divide [lcml xs]. *)
Lemma lcm_seq_is_mult_of_all_ints : 
  forall (sq : seq nat) (a : nat), a \in sq -> exists k, lcml sq = k * a. 
Proof.
  intros xs x IN.
  induction xs as [ | z sq IH_DIVIDES]; first by easy.
  rewrite in_cons in IN.
  move : IN => /orP [/eqP EQ | IN].
  + apply /dvdnP.
    rewrite EQ /lcml.
    by apply int_divides_lcm_in_seq.
  + move : (IH_DIVIDES IN) => [k EQ].
    exists ((foldr lcmn 1 (z :: sq)) %/ (foldr lcmn 1 sq) * k).
    rewrite -mulnA -EQ divnK /lcml //.
    by apply lcm_seq_divides_lcm_super.
Qed.
