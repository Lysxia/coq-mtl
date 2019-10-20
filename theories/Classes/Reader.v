
From mtl.Classes Require Import Tactics Monad Trans.
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

(* The laws about [ask] only. *)
Class LawfulAsk r m `{Monad m} (ask : m r) : Prop :=
  { (* [ask] yields the same result when called at any point. *)
    ask_comm : forall a b (u : m a) (k : r -> a -> m b),
        (u   >>= fun x =>
         ask >>= fun z => k z x)
      = (ask >>= fun z =>
         u   >>= fun x => k z x)

    (* [ask] has no side effects: ignoring its result is the same as not calling it. *)
  ; ask_nullipotent : forall a (u : m a),
      ask >> u = u

    (* Multiple calls to [ask] yield the same result as a single call. *)
  ; ask_ask : forall a (k : r -> r -> m a),
        (ask >>= fun z1 => ask >>= fun z2 => k z1 z2)
      = (ask >>= fun z => k z z)
  }.

Class LawfulMonadReader r m `{Monad m} `{MonadReader r m} : Prop :=
  { lawful_ask :> LawfulAsk r m ask
  ; local_ask : forall f,
      local f ask = (ask >>= fun z => pure (f z))

  ; local_const : forall (f : r -> r) a (u : m a),
      local f u = (ask >>= fun z => local (fun _ => f z) u)

    (* [local] is a monoid morphism between (reversed) [r -> r] and [m a -> m a]. *)
  ; local_id : forall a (u : m a),
      local (fun x => x) u = u
  ; local_local : forall (f g : r -> r) a (u : m a),
      local f (local g u) = local (fun z => g (f z)) u

    (* [local f] is a monad morphism between [m] and [m]. *)
  ; local_morphism :> forall f, MonadMorphism m m (local f)
  }.

Section ReaderFacts.

Context {r m}.
Context `{Monad m}.
Context {LM : LawfulMonad m}.
Context`{MonadReader r m}.
Context {LMR : LawfulMonadReader r m}.

Lemma local_const_k (f : r -> r) a (k : r -> m a)
  : (ask >>= fun z => local (fun _ => f z) (k z))
  = ask >>= fun z => local f (k z).
Proof.
  srewrite (local_const f, ask_ask). reflexivity.
Qed.

End ReaderFacts.
