From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All Retract.
From mtl.Monads Require Import State Reader Writer.

Implicit Types s e a : Type.
Implicit Types m : Type -> Type.

Module StateReader.
Section StateReaderS.

Context {s : Type} {m : Type -> Type} `{Monad m}.

Definition retract : forall a, StateT s m a -> ReaderT s m a :=
  fun a u => MkReaderT (fun z => runStateT u z >>= fun xz => pure (fst xz)).

Definition section : forall a, ReaderT s m a -> StateT s m a :=
  fun a u => MkStateT (fun z => runReaderT u z >>= fun x => pure (x, z)).

Instance SemiIso_ {LM : LawfulMonad m} : SemiIso retract section.
Proof.
  red; intros; apply injective_runReaderT, functional_extensionality; intros; cbn.
  rewrite bind_assoc; cbn.
  transitivity (runReaderT u x >>= pure).
  - f_equal; apply functional_extensionality; intros; rewrite bind_pure_l; reflexivity.
  - rewrite bind_pure_r; reflexivity.
Qed.

Instance MonadMorphism_section {LM : LawfulMonad m} :
  @MonadMorphism _ _ (Monad_Retract retract section) _ section.
Proof.
  split; intros; apply injective_runStateT, functional_extensionality; intros; cbn.
  - rewrite !bind_pure_l; reflexivity.
  - rewrite !bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite !bind_pure_l, !bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite !bind_pure_l; reflexivity.
Qed.

(** The default instance of [Monad] for [ReaderT] coincides with the one
    obtained by retraction. *)
Theorem MonadRetract_eq {LM : LawfulMonad m} :
  Monad_Retract retract section = Monad_ReaderT.
Proof.
  unfold Monad_Retract, Monad_ReaderT. f_equal.
  all: repeat (apply functional_extensionality_dep; intros).
  all: apply injective_runReaderT, functional_extensionality; intros; cbn.
  - rewrite bind_pure_l; reflexivity.
  - rewrite !bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l, bind_assoc.
    transitivity (runReaderT (x2 x4) x3 >>= pure).
    + f_equal; apply functional_extensionality; intros.
      rewrite bind_pure_l; reflexivity.
    + rewrite bind_pure_r; reflexivity.
Qed.

Instance MonadErrorMorphism_section {e}
  {LM : LawfulMonad m} {ME : MonadError e m} {LME : LawfulMonadError e m} :
  MonadErrorMorphismSection retract section.
Proof.
  split; intros; apply injective_runStateT, functional_extensionality; intros; cbn.
  - rewrite !left_zero_throw; reflexivity.
  - rewrite bind_assoc.
    replace (fun xz => _ >>= _) with (fun za : a * s => pure (fst za, x)).
    2: apply functional_extensionality; intros []; rewrite bind_pure_l; reflexivity.
    pose proof natural_catch as NC. unfold mapM in NC. rewrite NC. clear NC.
    f_equal. 2: apply functional_extensionality; intros.
    all: rewrite bind_assoc; f_equal; apply functional_extensionality; intros;
      rewrite bind_pure_l; reflexivity.
Qed.

(** The default instance of [MonadError] for [ReaderT] coincides with the one
    obtained by retraction. *)
Theorem MonadErrorRetract_eq {e}
  {LM : LawfulMonad m} `{MonadError e m} {LME : LawfulMonadError e m} :
  MonadError_Retract retract section = MonadError_ReaderT.
Proof.
  unfold MonadError_Retract, MonadError_ReaderT. f_equal.
  all: repeat (apply functional_extensionality_dep; intros).
  all: apply injective_runReaderT, functional_extensionality; intros; cbn.
  - rewrite left_zero_throw; reflexivity.
  - pose proof natural_catch as NC. unfold mapM in NC. rewrite NC. clear NC.
    f_equal. 2: apply functional_extensionality; intros.
    all: rewrite bind_assoc.
    all: replace (fun xz => _) with (fun z => pure z : m x)
      by (apply functional_extensionality; intros; rewrite bind_pure_l; reflexivity).
    all: rewrite bind_pure_r; reflexivity.
Qed.

End StateReaderS.
End StateReader.

Module StateWriter.
Section StateWriterS.

Context {s : Type} `{Monoid s} {m : Type -> Type} `{Monad m}.

Definition retract : forall a, StateT s m a -> WriterT s m a :=
  fun a u => MkWriterT (runStateT u mempty >>= fun xz => pure (snd xz, fst xz)).

Definition section : forall a, WriterT s m a -> StateT s m a :=
  fun a u => MkStateT (fun z => runWriterT u >>= fun zx => pure (snd zx, (z ++ fst zx)%monoid)).

Instance SemiIso_ {LM0 : LawfulMonoid s} {LM : LawfulMonad m} : SemiIso retract section.
Proof.
  red; intros; apply injective_runWriterT; intros; cbn.
  rewrite bind_assoc; cbn.
  transitivity (runWriterT u >>= pure).
  - f_equal; apply functional_extensionality; intros [].
    rewrite bind_pure_l, mappend_mempty_l; reflexivity.
  - rewrite bind_pure_r; reflexivity.
Qed.

Instance MonadMorphism_section {LM0 : LawfulMonoid s} {LM : LawfulMonad m} :
  @MonadMorphism _ _ (Monad_Retract retract section) _ section.
Proof.
  split; intros; apply injective_runStateT, functional_extensionality; intros; cbn.
  - rewrite !bind_pure_l; cbn; rewrite mappend_mempty_r; reflexivity.
  - rewrite !bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite !bind_pure_l, !bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite !bind_pure_l; cbn; rewrite mappend_mempty_l, mappend_assoc; reflexivity.
Qed.

(** The default instance of [Monad] for [ReaderT] coincides with the one
    obtained by retraction. *)
Theorem MonadRetract_eq {LM0 : LawfulMonoid s} {LM : LawfulMonad m} :
  Monad_Retract retract section = Monad_WriterT.
Proof.
  unfold Monad_Retract, Monad_WriterT. f_equal.
  all: repeat (apply functional_extensionality_dep; intros).
  all: apply injective_runWriterT; intros; cbn.
  - rewrite bind_pure_l; reflexivity.
  - rewrite !bind_assoc; f_equal; apply functional_extensionality; intros [].
    rewrite bind_pure_l, bind_assoc, mappend_mempty_l; cbn.
    f_equal; apply functional_extensionality; intros [].
    rewrite bind_pure_l; reflexivity.
Qed.

Instance MonadErrorMorphism_section {e} {LM0 : LawfulMonoid s}
  {LM : LawfulMonad m} {ME : MonadError e m} {LME : LawfulMonadError e m} :
  MonadErrorMorphismSection retract section.
Proof.
  split; intros; apply injective_runStateT, functional_extensionality; intros; cbn.
  - rewrite !left_zero_throw; reflexivity.
  - rewrite bind_assoc.
    replace (fun xz => _ >>= _) with (fun az : a * s => pure (fst az, (x ++ snd az)%monoid)).
    2: apply functional_extensionality; intros []; rewrite bind_pure_l; reflexivity.
    pose proof natural_catch as NC. unfold mapM in NC. rewrite NC. clear NC.
    f_equal. 2: apply functional_extensionality; intros.
    all: rewrite bind_assoc; f_equal; apply functional_extensionality; intros;
      rewrite bind_pure_l, mappend_mempty_l; reflexivity.
Qed.

(** The default instance of [MonadError] for [ReaderT] coincides with the one
    obtained by retraction. *)
Theorem MonadErrorRetract_eq {e} {LM0 : LawfulMonoid s}
  {LM : LawfulMonad m} `{MonadError e m} {LME : LawfulMonadError e m} :
  MonadError_Retract retract section = MonadError_WriterT.
Proof.
  unfold MonadError_Retract, MonadError_WriterT. f_equal.
  all: repeat (apply functional_extensionality_dep; intros).
  all: apply injective_runWriterT; intros; cbn.
  - rewrite left_zero_throw; reflexivity.
  - pose proof natural_catch as NC. unfold mapM in NC. rewrite NC. clear NC.
    f_equal. 2: apply functional_extensionality; intros.
    all: rewrite bind_assoc.
    all: replace (fun zx => _) with (fun zx : s * x => pure zx : m (s * x)%type)
      by (apply functional_extensionality; intros []; rewrite bind_pure_l, mappend_mempty_l; reflexivity).
    all: rewrite bind_pure_r; reflexivity.
Qed.

End StateWriterS.
End StateWriter.
