(** * The continuation monad transformer *)

From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All.

Record ContT (r : Type) m (a : Type) : Type :=
  MkContT { runContT : (a -> m r) -> m r }.

Arguments MkContT {r m a} _.
Arguments runContT {r m a} _.

Instance Monad_ContT {r m} : Monad (ContT r m) :=
  {| pure _ x := MkContT (fun yield => yield x)
   ; bind _ _ u k := MkContT (fun yield =>
       runContT u (fun x =>
       runContT (k x) yield))
  |}.

Instance MonadTrans_ContT {r} : MonadTrans (ContT r) :=
  {| lift _ _ _ u := MkContT (fun yield => u >>= yield)
  |}.

Instance MonadState_ContT {r s m} `{Monad m} `{MonadState s m} :
  MonadState s (ContT r m) :=
  MonadState_MonadTrans.

Lemma injective_runContT {r m a} (u v : ContT r m a) :
  runContT u = runContT v -> u = v.
Proof.
  destruct u, v; cbn; intros []; reflexivity.
Qed.

Instance LawfulMonad_ContT {r m} : LawfulMonad (ContT r m).
Proof.
  split; intros; apply injective_runContT, functional_extensionality; intros; cbn;
    reflexivity.
Qed.

Instance LawfulMonadTrans_ContT {r} : LawfulMonadTrans (ContT r).
Proof.
  split; intros; apply injective_runContT, functional_extensionality; intros; cbn.
  - rewrite bind_pure_l; reflexivity.
  - rewrite bind_assoc; reflexivity.
Qed.

Instance LawfulMonadState_ContT {r s m}
  `{LawfulMonad m} `{MonadState s m} {LMS : LawfulMonadState s m} :
  LawfulMonadState s (ContT r m) :=
  LawfulMonadState_LawfulMonadTrans.
