
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

(* The laws about [ask] only. *)
Class LawfulAsk r m `{Monad m} (ask : m r) : Prop :=
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
  }.

Class LawfulMonadReader r m `{Monad m} `{MonadReader r m} : Prop :=
  { lawful_ask :> LawfulAsk r m ask
  ; local_ask : forall f,
      local f ask = (ask >>= fun z => pure (f z))

    (* [local] is a monoid morphism between (reversed) [r -> r] and [m a -> m a]. *)
  ; local_id : forall a (u : m a),
      local (fun x => x) u = u
  ; local_compose : forall (f g : r -> r) a (u : m a),
      local f (local g u) = local (fun z => g (f z)) u

    (* [local f] is a monad morphism between [m] and [m]. *)
  ; local_morphism :> forall f, MonadMorphism m m (local f)
  }.

Section ReaderFacts.

Context {r m}.
Context `{Monad m}.
Context {LM : LawfulMonad m}.

Section AskFacts.

Context {ask : m r}.
Context {LA : LawfulAsk r m ask}.

Lemma ask_comm_k a b (u : m a) (k : r -> a -> m b)
  : (ask >>= fun z =>
     u   >>= fun x => k z x)
  = (u   >>= fun x =>
     ask >>= fun z => k z x).
Proof.
  transitivity ((ask >>= fun z => u >>= fun x => pure (z, x)) >>= fun zx => k (fst zx) (snd zx));
    [ | rewrite ask_comm ].
  all: do 2 (rewrite bind_assoc; f_equal; apply functional_extensionality; intros);
    rewrite bind_pure_l; reflexivity.
Qed.

Lemma ask_ask_k a (k : r -> r -> m a)
  : (ask >>= fun z1 => ask >>= fun z2 => k z1 z2)
  = (ask >>= fun z => k z z).
Proof.
  transitivity ((ask >>= fun z => pure (z, z)) >>= fun zz => k (fst zz) (snd zz)).
  - rewrite <- ask_ask.
    do 2 (rewrite bind_assoc; f_equal; apply functional_extensionality; intros).
    rewrite bind_pure_l; reflexivity.
  - rewrite bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l; reflexivity.
Qed.

End AskFacts.

Context`{MonadReader r m}.
Context {LMR : LawfulMonadReader r m}.

End ReaderFacts.
