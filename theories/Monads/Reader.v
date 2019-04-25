(** * The reader monad transformer *)

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

Instance LawfulMonadError_ReaderT {r e m} `{LawfulMonadError e m} :
  LawfulMonadError e (ReaderT r m).
Proof.
  destruct H1.
  split; intros; apply injective_runReaderT, functional_extensionality; cbn; intros;
    auto.
  rewrite catch_throw; reflexivity.
Qed.
