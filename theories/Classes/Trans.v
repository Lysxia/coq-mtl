(** * Monad transformers *)

From mtl.Classes Require Import
  Monad.

Implicit Types t : (Type -> Type) -> (Type -> Type).
Implicit Types m n : Type -> Type.

Class MonadTrans t : Type :=
  { lift : forall m (Monad_m : Monad m) a, m a -> t m a
  }.
(** Another possibility is to add a [LawfulMonad] constraint:
    [lift] might need the lawfulness (I have no examples).
  *)

Arguments lift {t _ m Monad_m} [a].

Class MonadMorphism m n `{Monad m} `{Monad n} (f : forall a, m a -> n a) : Prop :=
  { morphism_pure : forall a (x : a), f _ (pure x) = pure x
  ; morphism_bind : forall a b (u : m a) (k : a -> m b),
      f _ (bind u k) = bind (f _ u) (fun x => f _ (k x))
  }.

Notation LawfulMonadTrans t := (forall m `{LawfulMonad m}, MonadMorphism m (t m) lift).
