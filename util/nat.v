Require Import rt.util.tactics rt.util.ssromega.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.

(* Additional lemmas about natural numbers. *)
Section NatLemmas.
  
  Lemma addnb (b1 b2 : bool) : (b1 + b2) != 0 = b1 || b2.
  Proof.
    by destruct b1,b2;
    rewrite ?addn0 ?add0n ?addn1 ?orTb ?orbT ?orbF ?orFb.
  Qed.

  Lemma subh1 :
    forall m n p,
      m >= n ->
      m - n + p = m + p - n.
  Proof. by ins; ssromega. Qed.

  Lemma subh2 :
    forall m1 m2 n1 n2,
      m1 >= m2 ->
      n1 >= n2 ->
      (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2).
  Proof. by ins; ssromega. Qed.
  
  Lemma subh3:
    forall m n p,
      m + p <= n ->
      m <= n - p.
  Proof.
    clear.
    intros.
    rewrite <- leq_add2r with (p := p).
    rewrite subh1 //.
    - by rewrite -addnBA // subnn addn0.
    - by apply leq_trans with (m+p); first rewrite leq_addl.
  Qed.

  Lemma subh4:
    forall m n p,
      m <= n ->
      p <= n ->
      (m == n - p) = (p == n - m).
  Proof.
    intros; apply/eqP.
    destruct (p == n - m) eqn:EQ.
      by move: EQ => /eqP EQ; rewrite EQ subKn.
      by apply negbT in EQ; unfold not; intro BUG;
        rewrite BUG subKn ?eq_refl in EQ.
  Qed.

  Lemma addmovr:
    forall m n p,
      m >= n ->
      (m - n = p <-> m = p + n).
  Proof.
    by split; ins; ssromega.
  Qed.

  Lemma addmovl:
    forall m n p,
      m >= n ->
      (p = m - n <-> p + n = m).
  Proof.
    by split; ins; ssromega.
  Qed.

  Lemma ltSnm : forall n m, n.+1 < m -> n < m.
  Proof.
    by ins; apply ltn_trans with (n := n.+1); [by apply ltnSn |by ins].
  Qed.
  
  Lemma min_lt_same :
    forall x y z,
      minn x z < minn y z -> x < y.
  Proof.
    unfold minn; ins; desf.
    {
      apply negbT in Heq0; rewrite -ltnNge in Heq0.
      by apply leq_trans with (n := z).
    }
    {
      apply negbT in Heq; rewrite -ltnNge in Heq.
      by apply (ltn_trans H) in Heq0; rewrite ltnn in Heq0.
    }
    by rewrite ltnn in H.
  Qed.

  Lemma add_subC:
    forall a b c,
      a >= c ->
      b >=c ->
      a + (b - c ) = a - c + b.
  Proof.
    intros* AgeC BgeC.
    induction b;induction c;intros;try ssromega.
  Qed.

  Lemma ltn_subLR:
    forall a b c,
      a - c < b ->
      a < b + c.
  Proof.
    intros* AC. ssromega.
  Qed.
  
End NatLemmas.