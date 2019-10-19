
From mtl.Classes Require Import Monad Trans.
From Coq Require Import Setoid FunctionalExtensionality Relations Morphisms.

Implicit Types t : (Type -> Type) -> (Type -> Type).
Implicit Types m : Type -> Type.
Implicit Types r a : Type.

Class MonadReader r m : Type :=
  { ask : m r
  ; local : (r -> r) -> forall a, m a -> m a
  }.

Arguments local {r m _} _ [a].

Definition reader {r m} `{Monad m} `{MonadReader r m} {a} (f : r -> a) : m a :=
  ask >>= fun z => pure (f z).

Class LawfulMonadReader r m `{Monad m} `{MonadReader r m} : Type :=
  { (* [ask] yields the same result when called at any point. *)
    ask_comm : forall a (u : m a),
        (ask >>= fun z =>
         u   >>= fun x => pure (z, x))
      = (u   >>= fun x =>
         ask >>= fun z => pure (z, x))

    (* [ask] has no side effects: ignoring its result is the same as not calling it. *)
  ; ask_nullipotent : forall a (u : m a),
      ask >> u = u

    (* Multiple calls to [ask] yield the same result as a single call. *)
  ; ask_ask
      : (ask >>= fun z1 => ask >>= fun z2 => pure (z1, z2))
      = (ask >>= fun z => pure (z, z))

  ; local_ask : forall f,
      local f ask = (ask >>= fun z => pure (f z))

    (* [local] is a monoid morphism between [r -> r] and [m a -> m a]. *)
  ; local_id : forall a (u : m a),
      local (fun x => x) u = u
  ; local_compose : forall (f g : r -> r) a (u : m a),
      local f (local g u) = local (fun z => f (g z)) u

    (* [local f] is a monad morphism between [m] and [m]. *)
  ; local_morphism :> forall f, MonadMorphism m m (local f)
  }.

Section ReaderFacts.

Context r m.
Context `{Monad m} `{MonadReader r m}.
Context {LM : LawfulMonad m}.
Context {LMR : LawfulMonadReader r m}.

End ReaderFacts.
