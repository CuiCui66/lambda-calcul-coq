
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

Example ident : substi (var 0) 0 identity = identity.
simpl. trivial. Qed.

Fixpoint beta_reduction (t1 : lterm) (t2 : lterm) : Prop := 
match (t1,t2) with
| (var _,var _) => False
| (abs l1, abs l2) => beta_reduction l1 l2
| (app u1 v1, app u2 v2) =>    (u1 = u2 /\ beta_reduction v1 v2)
                            \/ (beta_reduction u1 u2 /\ v1 = v2)
                            \/ substi u1 0 v1 = t2
| (app u v, _) => substi u 0 v = t2
| (_,_) => False
end.

Fixpoint beta_eq' (n : nat) (t1 : lterm) (t2 : lterm) : Prop :=
match n with
| 0 => False
| S n' =>    t1 = t2
          \/ beta_reduction t1 t2
          \/ beta_reduction t2 t1
          \/ (exists t3, beta_reduction t1 t3 /\ beta_eq' n' t3 t2)
          \/ (exists t3, beta_reduction t2 t3 /\ beta_eq' n' t1 t3)
end.

Definition beta_eq (t1 : lterm) (t2 : lterm) : Prop :=
    exists (n : nat), beta_eq' n t1 t2.

