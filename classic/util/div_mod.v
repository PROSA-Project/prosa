Require Export prosa.util.div_mod.

Require Import Arith Omega Nat.
Require Import prosa.classic.util.tactics prosa.util.ssromega prosa.classic.util.nat.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div.


  Definition div_floor (x y: nat) : nat := x %/ y.
  Definition div_ceil (x y: nat) := if y %| x then x %/ y else (x %/ y).+1.

  Lemma ltn_div_trunc :
    forall m n d,
      d > 0 ->
      m %/ d < n %/ d ->
      m < n.
  Proof.
    intros m n d GT0 DIV; rewrite ltn_divLR in DIV; last by ins.
    by apply leq_trans with (n := n %/ d * d);
      [by ins| by apply leq_trunc_div].
  Qed.
  
  Lemma subndiv_eq_mod:
    forall n d, n - n %/ d * d = n %% d.
  Proof.
    by ins; rewrite {1}(divn_eq n d) addnC -addnBA // subnn addn0.
  Qed.

  Lemma divSn_cases :
    forall n d,
      d > 1 ->
      (n %/ d = n.+1 %/d /\ n %% d + 1 = n.+1 %% d) \/
      (n %/ d + 1 = n.+1 %/ d).
  Proof.
    ins; set x := n %/ d; set y := n %% d.
    assert (GT0: d > 0); first by apply ltn_trans with (n := 1).
    destruct (ltngtP y (d - 1)) as [LTN | BUG | GE]; [left | | right];
      first 1 last.
    {
      exploit (@ltn_pmod n d); [by apply GT0 | intro LTd; fold y in LTd].
      rewrite -(ltn_add2r 1) [y+1]addn1 ltnS in BUG.
      rewrite subh1 in BUG; last by apply GT0.
      rewrite -addnBA // subnn addn0 in BUG.
      by apply (leq_ltn_trans BUG) in LTd; rewrite ltnn in LTd.
    }

    {
      (* Case 1: y = d - 1*)
      move: GE => /eqP GE; rewrite -(eqn_add2r 1) in GE.
      rewrite subh1 in GE; last by apply GT0.
      rewrite -addnBA // subnn addn0 in GE.
      move: GE => /eqP GE.
      apply f_equal with (f := fun x => x %/ d) in GE.
      rewrite divnn GT0 /= in GE.
      unfold x; rewrite -GE.
      rewrite -divnMDl; last by apply GT0.
      f_equal; rewrite addnA.
      by rewrite -divn_eq addn1.
    }
    {
      assert (EQDIV: n %/ d = n.+1 %/ d).
      {
        apply/eqP; rewrite eqn_leq; apply/andP; split;
          first by apply leq_div2r, leqnSn.
        rewrite leq_divRL; last by apply GT0.
        rewrite -ltnS {2}(divn_eq n.+1 d).
        rewrite -{1}[_ %/ d * d]addn0 ltn_add2l.
        unfold y in *.
        rewrite ltnNge; apply/negP; unfold not; intro BUG.
        rewrite leqn0 in BUG; move: BUG => /eqP BUG.
        rewrite -(modnn d) -addn1 in BUG.
        destruct d; first by rewrite sub0n in LTN.
        move: BUG; move/eqP; rewrite -[d.+1]addn1 eqn_modDr [d+1]addn1; move => /eqP BUG.
        rewrite BUG -[d.+1]addn1 -addnBA // subnn addn0 in LTN.
        by rewrite modn_small in LTN;
          [by rewrite ltnn in LTN | by rewrite addn1 ltnSn].
      }
      (* Case 2: y < d - 1 *)
      split; first by rewrite -EQDIV.
      {
        unfold x, y in *.
        rewrite -2!subndiv_eq_mod.
        rewrite subh1 ?addn1; last by apply leq_trunc_div.
        rewrite EQDIV; apply/eqP.
        rewrite -(eqn_add2r (n%/d*d)).
        by rewrite subh1; last by apply leq_trunc_div.
      }
    }
  Qed.

  Lemma ceil_neq0 :
    forall x y,
      x > 0 ->
      y > 0 ->
      div_ceil x y > 0.
  Proof.
    unfold div_ceil; intros x y GEx GEy.
    destruct (y %| x) eqn:DIV; last by done.
    by rewrite divn_gt0; first by apply dvdn_leq.
  Qed.

  Lemma leq_divceil2r :
    forall d m n,
      d > 0 ->
      m <= n ->
      div_ceil m d <= div_ceil n d.
  Proof.
    unfold div_ceil; intros d m n GT0 LE.
    destruct (d %| m) eqn:DIVm, (d %| n) eqn:DIVn;
      [by apply leq_div2r | | | by apply leq_div2r].
    by apply leq_trans with (n := n %/ d); first by apply leq_div2r.
    {
      rewrite leq_eqVlt in LE; move: LE => /orP [/eqP EQ | LT];
        first by subst; rewrite DIVn in DIVm.
      rewrite ltn_divLR //.
      apply leq_trans with (n := n); first by done.
      by apply eq_leq; symmetry; apply/eqP; rewrite -dvdn_eq.    
    }
  Qed.

(* Versions of eqn_modDl and eqn_modDl in Prop *)

  Lemma eq_modDl: forall p m n d, (p + m = p + n %[mod d]) <-> (m = n %[mod d]).
  Proof.
    split; intro G.
    - apply /eqP. rewrite <- eqn_modDl with (p:=p).
      by apply /eqP. 
    - rewrite -modnDm G. 
      by rewrite modnDm.
  Qed.

  Lemma eq_modDr: forall p m n d, (m + p = n + p %[mod d]) <-> (m = n %[mod d]).
  Proof.
    split; intro G.
    - apply /eqP. rewrite <- eqn_modDr with (p:=p).
      by apply /eqP.
    - rewrite -modnDm G. 
      by rewrite modnDm.
  Qed.

  (* If a(n)= b+a (n) then b is a multiple of c 
    Proposed name modnD_k *)

  Lemma modulo_exists: forall a b c,
    c>0 -> a = b + a %[mod c] -> exists k, b = k*c.
  Proof.
    intros* F G.
    change a with (0+a) in G.
    apply eq_modDr in G.
    rewrite mod0n in G.
    assert (X: b = b%/c *c + b%%c) by apply divn_eq.
    rewrite -G addn0 in X. 
    by exists (b%/c).
  Qed.

  (* If (a+1)[n+1]=0 then a[n+1]=n *)
  Lemma modnS_eq : forall a n, a.+1 %% n.+1 =0 <-> a %% n.+1 = n.
  Proof.
    intros.
    rewrite -(modnn (n.+1)).
    change (a.+1) with (1+a).
    change (n.+1) with (1+n).
    assert (X:n<n.+1) by ssromega.
    apply modn_small in X.
    split; intros* G.
    - apply eq_modDl in G.
      by rewrite G.
    - apply eq_modDl.
      by rewrite G.
  Qed.

  (* Incrementing the integer under a modulo either increments the result or yields 0 *)

  Lemma modnSor': forall a n, a.+1 %% n = (a %% n).+1 \/ (a.+1 %% n =0).
  Proof.
    intros*.
    destruct (ltngtP ((a%%n).+1) (n)) as [G|G|G].
    - left. apply modn_small in G.
      by rewrite -G -addn1 -modnDml addn1.
    - destruct n.
      + left. reflexivity.
      + assert (X: a%%n.+1 < n.+1). by apply ltn_pmod. ssromega.
    - right. destruct n.
      + discriminate G.
      + apply modnS_eq. by injection G. 
  Qed.

  Lemma modnSor: forall a n, a.+1 %% n.+1 = (a %% n.+1).+1 \/ (a.+1 %% n.+1 =0).
  Proof.
    intros.
    destruct (ltngtP ((a%%n.+1).+1) (n.+1)) as [G|G|G].
    - left. apply modn_small in G.
      by rewrite -G -addn1 -modnDml addn1.
    - assert (X: a%%n.+1 < n.+1). by apply ltn_pmod. ssromega.
    - right. apply modnS_eq. ssromega. 
  Qed.

  (* Old version of the lemma which is now covered by modnSor and modnS_eq *)

  Lemma modulo_cases : forall a c,
    a.+1 %% c.+1 = (a %% c.+1).+1 \/ (a.+1 %% c.+1 =0 /\ a %% c.+1 =c).
  Proof.
    intros. destruct (modnSor a c) as [G|G]; try by left.
    right; split; try done.
    by apply modnS_eq.
  Qed.

  Lemma ceil_eq1: forall a c, a > 0 -> a <= c -> div_ceil a c = 1.
  Proof.
    intros* G1. unfold div_ceil.
    rewrite leq_eqVlt. move/orP => [G2|G2].
    - move/eqP :G2 => G2. subst.
      rewrite dvdnn. rewrite divnn. 
      destruct c; ssromega.
    - rewrite gtnNdvd // divn_small //.
  Qed.

  Lemma ceil_suba: forall a c, c > 0 -> a > c -> div_ceil a c = (div_ceil (a-c) c).+1.
  Proof.
    intros* G1 G2. unfold div_ceil.
    assert (X:a=a-c+c) by (rewrite subnK //; ssromega).
    case E1:(c %| a); case E2:(c %| a - c); rewrite {1} X.  
    - rewrite divnDl //. rewrite divnn. by rewrite G1 addn1.
    - rewrite X in E1. apply dvdn_add_eq in E1. 
      rewrite dvdnn E2 in E1. inversion E1.
    - apply dvdn_addr with (n:=c) in E2. 
      rewrite dvdnn in E2. rewrite X E2 in E1. inversion E1.
    - rewrite divnDr // divnn G1 addn1 //.
  Qed.

  Lemma mod_eq: forall a b, a%%b = a - a%/b * b.
  Proof.
    intros.
    rewrite {2}(divn_eq a b).
    ssromega.
  Qed.
