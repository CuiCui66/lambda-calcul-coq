
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

Print beq_nat.

Fixpoint substi (t :lterm) (n: nat) (sub : lterm) : lterm :=
  match t with
  | var m => if beq_nat n m then term_map (fun x => x+n) sub else var m 
  | app t1 t2 => app (substi t1 n sub) (substi t2 n sub)
  | abs t0 => abs (substi t0 (S n) sub)
  end.



