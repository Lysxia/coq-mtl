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

Instance MonadReader_ContT {r s m} `{Monad m} `{MonadReader s m} :
  MonadReader s (ContT r m) :=
  { ask := lift ask
  ; local := fun f _ u => MkContT (fun k =>
      ask >>= fun z => local f (runContT u (fun x => local (fun _ => z) (k x))))
  }.

Instance Proper_runCont {r m a}
  : Proper (eq ==> pw eq ==> eq) (runContT (r := r) (m := m) (a := a)).
Proof.
  repeat intro; f_equal; auto using functional_extensionality.
Qed.

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

Instance LawfulMonadReader_ContT {r s m}
  `{LawfulMonad m} `{MonadReader s m} {LMS : LawfulMonadReader s m} :
  LawfulMonadReader s (ContT r m).
Proof.
  (* We need to quantify over computations [u] that satisfy [ask_comm] (which is sufficient
     to derive proofs of other laws). *)
  assert (comm : forall a (u : ContT r m a) (k : s -> a -> m r),
    (ask >>= fun z => runContT u (fun x => k z x)) = runContT u (fun x => ask >>= fun z => k z x)).
  { admit. }
  repeat split; intros; apply injective_runContT; cbn; apply functional_extensionality; intros.
  - rewrite comm. reflexivity.
  - srewrite (comm, ask_nullipotent). reflexivity.
  - rewrite ask_ask_k. reflexivity.
  - srewrite (morphism_bind, local_ask, bind_assoc, bind_pure_l, local_local, ask_ask_k, local_const_k).
    reflexivity.
  - srewrite (ask_ask_k, local_const_k, comm, local_const). reflexivity.
  - srewrite (local_id, comm, local_const). reflexivity.
  - srewrite (morphism_bind, local_ask, bind_assoc, bind_pure_l, ask_ask_k, local_local, local_local).
    reflexivity.
  - srewrite (local_local, local_const). reflexivity.
  - admit.
Abort.
