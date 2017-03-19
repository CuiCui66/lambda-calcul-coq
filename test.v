
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


