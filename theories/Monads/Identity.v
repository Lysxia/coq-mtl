From mtl.Classes Require Import Monad.

Record Identity (a : Type) : Type :=
  MkIdentity { runIdentity : a }.

Arguments MkIdentity {a} _.
Arguments runIdentity {a} _.

Instance Monad_Identity : Monad Identity :=
  { pure _ := MkIdentity
  ; bind _ _ u k := k (runIdentity u)
  }.
