(** * The reader monad transformer *)

(** In this file:
  - The [ReaderT] monad transformer.
  - Instances:
    + [Monad], [LawfulMonad]
    + [MonadTrans], [LawfulMonadTrans]
    + [MonadState], [LawfulMonadState]
    + [MonadReader], [LawfulMonadReader]
    + [MonadError], [LawfulMonadError]
  - Completeness for [ask] laws ([LawfulAsk]):
    they are equivalent to saying that there is a monad morphism from [ReaderT r m] to [m]
    compatible to [lift].
 *)

From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All.

Implicit Types r a : Type.
Implicit Types m : Type -> Type.

Record ReaderT r m a : Type :=
  MkReaderT { runReaderT : r -> m a }.

Arguments MkReaderT {r m a} _.
Arguments runReaderT {r m a} _.

(** ** Instances *)

Instance Monad_ReaderT {r m} `{Monad m} : Monad (ReaderT r m) :=
  {| pure _ x := MkReaderT (fun _ => pure x)
   ; bind _ _ u k := MkReaderT (fun z =>
       runReaderT u z >>= fun x =>
       runReaderT (k x) z)
  |}.

Instance MonadTrans_ReaderT {r} : MonadTrans (ReaderT r) :=
  {| lift _ _ _ u := MkReaderT (fun _ => u)
  |}.

Instance MonadState_ReaderT {r s m} `{MonadState s m} : MonadState s (ReaderT r m) :=
  {| get := MkReaderT (fun _ => get)
   ; put z := MkReaderT (fun _ => put z)
  |}.

Instance MonadReader_ReaderT {r m} `{Monad m} : MonadReader r (ReaderT r m) :=
  {| ask := MkReaderT (fun z => pure z)
   ; local := fun f _ u => MkReaderT (fun z => runReaderT u (f z))
  |}.

Instance MonadError_ReaderT {r e m} `{MonadError e m} : MonadError e (ReaderT r m) :=
  {| throwError _ err := MkReaderT (fun _ => throwError err)
   ; catchError _ u h := MkReaderT (fun z =>
       catchError (runReaderT u z) (fun err => runReaderT (h err) z))
  |}.

(** ** Simple facts *)

Lemma injective_runReaderT {r m a} (u v : ReaderT r m a) :
  runReaderT u = runReaderT v -> u = v.
Proof.
  destruct u, v; cbn; intros []; reflexivity.
Qed.

(** ** Laws *)

Instance LawfulMonad_ReaderT {r m} `{LawfulMonad m} : LawfulMonad (ReaderT r m).
Proof.
  split; intros; apply injective_runReaderT, functional_extensionality; cbn; intros.
  - rewrite bind_pure_l; reflexivity.
  - rewrite bind_pure_r; reflexivity.
  - rewrite bind_assoc; reflexivity.
Qed.

Instance LawfulMonadTrans_ReaderT {r} : LawfulMonadTrans (ReaderT r).
Proof.
  split; intros; apply injective_runReaderT; reflexivity.
Qed.

Instance LawfulMonadState_ReaderT {r s m} `{LawfulMonadState s m} :
  LawfulMonadState s (ReaderT r m).
Proof.
  destruct H1.
  split; intros; apply injective_runReaderT, functional_extensionality; cbn; intros;
    auto.
Qed.

Instance LawfulMonadReader_ReaderT {r m} `{LawfulMonad m} :
  LawfulMonadReader r (ReaderT r m).
Proof.
  split; try split; intros; try apply injective_runReaderT, functional_extensionality; cbn; intros.
  all: repeat (rewrite ?bind_pure_l; reflexivity || f_equal; apply functional_extensionality; intros).
Qed.

Instance LawfulMonadError_ReaderT {r e m} `{LawfulMonadError e m} :
  LawfulMonadError e (ReaderT r m).
Proof.
  destruct H1.
  split; intros; apply injective_runReaderT, functional_extensionality; cbn; intros;
    auto.
  - rewrite catch_throw; reflexivity.
  - apply natural_catch.
Qed.

(** ** Characterization of lawful [ask] (without [local]) as a retraction from [ReaderT]. *)

Class MonadReader' r m : Type :=
  runReaderT' : forall a, ReaderT r m a -> m a.

Arguments runReaderT' {r m _} [a].

Class LawfulMonadReader' r m {M : Monad m} `{MR' : MonadReader' r m} : Type :=
  { MonadMorphism_runReaderT' :> MonadMorphism (ReaderT r m) m runReaderT'
  ; runReaderT'_lift : forall a (u : m a), runReaderT' (lift u) = u
  }.

Definition ask' {r m} `{Monad m} `{MonadReader' r m} : m r :=
  runReaderT' ask.

Lemma LawfulAsk_LawfulMonadReader' r m
  `{LawfulMonad m} `{LawfulMonadReader' r m (M := _)} : LawfulAsk r m ask'.
Proof.
  split; intros; unfold ask'.
  - transitivity (runReaderT' (lift u >>= fun x => ask >>= fun z => pure (z, x)));
      [ | transitivity (runReaderT' (ask >>= fun z => lift u >>= fun x => pure (z, x))) ].
    2: rewrite ask_comm; reflexivity.
    all: repeat (rewrite morphism_bind, ?runReaderT'_lift;
             f_equal; apply functional_extensionality; intros);
           rewrite morphism_pure; reflexivity.
  - transitivity (runReaderT' (ask >> lift u)).
    + srewrite (morphism_bind (f := runReaderT'), runReaderT'_lift); reflexivity.
    + rewrite ask_nullipotent, runReaderT'_lift; reflexivity.
  - evar (e1 : ReaderT r m (r * r)%type). evar (e2 : ReaderT r m (r * r)%type).
    transitivity (runReaderT' e1); [ | transitivity (runReaderT' e2); [ f_equal | ] ]; subst e1 e2.
    2: apply ask_ask.
    all: repeat (rewrite morphism_bind; f_equal; apply functional_extensionality; intros);
      rewrite morphism_pure; reflexivity.
Qed.

Definition MonadReader'_ask {r m} `{Monad m} (ask : m r) : MonadReader' r m :=
  fun _ u => ask >>= runReaderT u.

Lemma LawfulMonadReader'_LawfulAsk r m `{LawfulMonad m} (ask : m r) {LA : LawfulAsk r m ask}
  : @LawfulMonadReader' r m _ (MonadReader'_ask ask).
Proof.
  repeat split; intros; cbn; unfold runReaderT', MonadReader'_ask; cbn.
  1, 3: rewrite ask_nullipotent; reflexivity.
  - setoid_rewrite ask_comm_k. srewrite (bind_assoc, ask_ask_k).
    reflexivity.
Qed.
