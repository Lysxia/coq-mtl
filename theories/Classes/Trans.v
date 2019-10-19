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

Class LawfulMonadTrans t
  `{MonadTrans t}
  `{forall m, Monad m -> Monad (t m)}
  `{forall m `{LawfulMonad m}, LawfulMonad (t m)} : Prop :=
  lift_morphism :> forall m `{LawfulMonad m}, MonadMorphism m (t m) lift.

Class MonadFunctor t : Type :=
  mfmap : forall m n {Monad_m : Monad m} {Monad_n : Monad n},
    (forall a, m a -> n a) -> forall a, t m a -> t n a.

Class LawfulMonadFunctor t `{LawfulMonadTrans t} `{MonadFunctor t} : Prop :=
  { proper_monad_functor : forall m n `(LawfulMonad m) `(LawfulMonad n) f,
      MonadMorphism m n f ->
      MonadMorphism (t m) (t n) (mfmap m n f)

    (* Will probably need naturality *)
  }.
