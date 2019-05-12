From mtl.Classes Require Import Monad.

Record Identity (a : Type) : Type :=
  MkIdentity { runIdentity : a }.

Arguments MkIdentity {a} _.
Arguments runIdentity {a} _.

Lemma injective_runIdentity {a} (u v : Identity a)
  : runIdentity u = runIdentity v -> u = v.
Proof.
  destruct u, v; intros; f_equal; auto.
Qed.

Instance Monad_Identity : Monad Identity :=
  { pure _ := MkIdentity
  ; bind _ _ u k := k (runIdentity u)
  }.

Instance LawfulMonad_Identity : LawfulMonad Identity.
Proof.
  split; intros; apply injective_runIdentity; reflexivity.
Qed.
