(** * Monads *)

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

Infix ">>=" := bind (at level 50, left associativity).
Notation "u >> v" := (bind u (fun _ => v)) (at level 50, left associativity).

(** In theory, the laws are part of the definition of a "monad",
    so [LawfulMonad] is what should really be named [Monad], and the record
    of operations [Monad] should really be named something else
    ([PreMonad]? [Magmad]?).
  *)
