From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All Retract.
From mtl.Monads Require Import State Reader.

Implicit Types s : Type.
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
