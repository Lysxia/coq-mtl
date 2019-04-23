Implicit Types m : Type -> Type.

Class Monad m : Type :=
  { pure : forall a, a -> m a
  ; bind : forall a b, m a -> (a -> m b) -> m b
  }.

Arguments pure {m _ a} _.
Arguments bind {m _ a b} _ _.

Class LawfulMonad m `{Monad m} : Prop :=
  { bind_pure_l : forall a b (x : a) (k : a -> m b), bind (pure x) k = k x
  ; bind_pure_r : forall a (u : m a), bind u pure = u
  ; bind_assoc : forall a b c (u : m a) (k : a -> m b) (h : b -> m c),
      bind (bind u k) h = bind u (fun x => bind (k x) h)
  }.
