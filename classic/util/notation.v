Require Export prosa.util.notation.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Here we define a more verbose notation for projections of pairs... *)
Section Pair.

  Context {A B: Type}.
  Variable p: A * B.
  Definition pair_1st := fst p.
  Definition pair_2nd := snd p.

End Pair.

(* ...and triples. *)
Section Triple.

  Context {A B C: Type}.
  Variable p: A * B * C.
  Definition triple_1st (p: A * B * C) := fst (fst p).
  Definition triple_2nd := snd (fst p).
  Definition triple_3rd := snd p.

End Triple.

(* Define a wrapper from an element to a singleton list. *)
Definition make_sequence {T: Type} (opt: option T) :=
  match opt with
    | Some j => [:: j]
    | None => [::]
  end.
  
(* Let's define big operators for lists of pairs. *)

Reserved Notation "\sum_ ( ( m , n ) <- r ) F"
  (at level 41, F at level 41, m, n at level 50,
   format "'[' \sum_ ( ( m , n ) <- r ) '/ ' F ']'").

Notation "\sum_ ( ( m , n ) <- r ) F" :=
  (\sum_(i <- r) (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\sum_ ( ( m , n ) <- r | P ) F"
  (at level 41, F at level 30, P at level 41, m, n at level 50,
   format "'[' \sum_ ( ( m , n ) <- r | P ) '/ ' F ']'").

Notation "\sum_ ( ( m , n ) <- r | P ) F" :=
  (\sum_(i <- r | (let '(m,n) := i in P))
    (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\max_ ( ( m , n ) <- r ) F"
  (at level 41, F at level 41, m, n at level 50,
   format "'[' \max_ ( ( m , n ) <- r ) '/ ' F ']'").

Notation "\max_ ( ( m , n ) <- r ) F" :=
  (\max_(i <- r) (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\max_ ( ( m , n ) <- r | P ) F"
  (at level 41, F at level 30, P at level 41, m, n at level 50,
   format "'[' \max_ ( ( m , n ) <- r | P ) '/ ' F ']'").

Notation "\max_ ( ( m , n ) <- r | P ) F" :=
  (\max_(i <- r | (let '(m,n) := i in P))
    (let '(m,n) := i in F)) : nat_scope.

Notation "[ 'pairs' ( x , y ) <- s | C ]" :=
  (filter (fun i => let '(x,y) := i in C%B) s)
 (at level 0, x at level 99,
  format "[ '[hv' 'pairs' ( x , y ) <- s '/ ' | C ] ']'") : seq_scope.

Notation "[ 'pairs' ( E , F ) | x <- s ]" :=
    (map (fun y => ((fun x1 => let x := x1 in E) y, (fun x2 => let x := x2 in F) y)) s)
  (at level 0, E at level 1, F at level 1, 
   format "[ '[hv' 'pairs' ( E , F )  |  x  <-  s ] ']'") : seq_scope.

(* In case we use an (option list T), we can define membership
   without having to match the option type. *)
Reserved Notation "x \In A"
  (at level 70, format "'[hv' x '/ ' \In A ']'", no associativity).
Notation "x \In A" :=
  (if A is Some B then in_mem x (mem B) else false) : bool_scope.
