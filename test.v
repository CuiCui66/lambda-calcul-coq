
Inductive lterm : Set :=
|var  : nat -> lterm
|app : lterm -> lterm -> lterm
|abs : lterm -> lterm.

Inductive ltype : Set :=
| base : nat -> ltype
| fle : ltype -> ltype -> ltype.

Fixpoint term_map (f : nat -> nat) (t : lterm) : lterm :=
match t with
| var n     => var (f n)
| app t1 t2 => app (term_map f t1) (term_map f t2)
| abs t     => abs (term_map f t)
end.

Require Import Arith.

Print leb.
Fixpoint offset (t : lterm) (decal :nat) (limit : nat) : lterm :=
  match t with
  | var i => if leb i limit then var i else var (i+decal)
  | app t1 t2 => app (offset t1 decal limit) (offset t2 decal limit)
  | abs t0 => abs (offset t0 decal (S limit))
  end. 



Fixpoint substi (t :lterm) (n: nat) (sub : lterm) : lterm :=
  match t with
  | var m => if beq_nat n m then offset sub n 0 else var m 
  | app t1 t2 => app (substi t1 n sub) (substi t2 n sub)
  | abs t0 => abs (substi t0 (S n) sub)
  end.

Definition identity := abs (var 0).

Example ident : substi (var 0) 0 identity = identity

