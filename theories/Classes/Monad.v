(** * Monads *)

From mtl.Classes Require Import Tactics.

Implicit Types m : Type -> Type.

Class Monad m : Type :=
  { pure : forall a, a -> m a
  ; bind : forall a b, m a -> (a -> m b) -> m b
  }.

Arguments pure {m _ a} _.
Arguments bind {m _ a b} _ _.

Infix ">>=" := bind (at level 50, left associativity).
Notation "u >> v" := (bind u (fun _ => v)) (at level 50, left associativity).

Definition mapM {m} `{Monad m} {a b : Type} (f : a -> b) (u : m a) : m b :=
  u >>= fun x => pure (f x).

Class LawfulMonad m `{Monad m} : Prop :=
  { bind_pure_l : forall a b (x : a) (k : a -> m b), bind (pure x) k = k x
  ; bind_pure_r : forall a (u : m a), bind u pure = u
  ; bind_assoc : forall a b c (u : m a) (k : a -> m b) (h : b -> m c),
      bind (bind u k) h = bind u (fun x => bind (k x) h)
  }.

(** In theory, the laws are part of the definition of a "monad",
    so [LawfulMonad] is what should really be named [Monad], and the record
    of operations [Monad] should really be named something else
    ([PreMonad]? [Magmad]?).
  *)

Instance Proper_bind {m a b} `{Monad m}
  : Proper (eq ==> pw eq ==> eq) (bind (a := a) (b := b)).
Proof.
  repeat intro; f_equal; auto using functional_extensionality.
Qed.

(* From Goal [bind u k1 = bind u k2] get to goal [forall a, k1 a = k2 a]. *)
Ltac unbind :=
  lazymatch goal with
  | [ |- bind _ _ = bind _ _ ] => apply Proper_bind; try reflexivity; unfold pointwise_relation
  | _ => fail "Not an equality between bind"
  end.


(* Derived equations *)
Section MoreEquations.

Context {m} `{LawfulMonad m}.

Lemma bind_pure_bind a b c (u : m a) (f : a -> b) (k : b -> m c)
  : bind (bind u (fun x => pure (f x))) k = bind u (fun x => k (f x)).
Proof.
  rewrite bind_assoc; unbind; intros; rewrite bind_pure_l; reflexivity.
Qed.

End MoreEquations.
