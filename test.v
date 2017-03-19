
Inductive lterm : Set :=
|var  : nat -> lterm
|app : lterm -> lterm -> lterm
|abs : lterm -> lterm.

Inductive ltype : Set :=
| base : nat -> ltype
| fle : ltype -> ltype -> ltype.
