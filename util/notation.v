From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* We define a notation for the big concatenation operator.*)
  
 Reserved Notation "\cat_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n ) F" :=
  (\big[cat/[::]]_(m <= i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, P at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n | P ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n | P ) F" :=
  (\big[cat/[::]]_(m <= i < n | P) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n ) '/ ' F ']'").

Notation "\cat_ ( i < n ) F" :=
  (\big[cat/[::]]_(i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n | P ) '/ ' F ']'").

Notation "\cat_ ( i < n | P ) F" :=
  (\big[cat/[::]]_(i < n | P) F%N) : nat_scope.
  