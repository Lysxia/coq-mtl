(** Selection monad transformer *)

(* begin hide *)
From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All.
(* end hide *)

Implicit Types r a : Type.
Implicit Types m : Type -> Type.

Record SelectT r m a : Type :=
  MkSelectT { runSelectT : (a -> m r) -> m a }.

Arguments MkSelectT {r m a} _.
Arguments runSelectT {r m a} _.

(** Instances *)

Instance Monad_SelectT {r m} `{Monad m} : Monad (SelectT r m) :=
  {| pure _ x := MkSelectT (fun _ => pure x)
   ; bind _ _ u k := MkSelectT (fun yield =>
       let h x := runSelectT (k x) yield in
       runSelectT u (fun x => h x >>= yield) >>= h)
  |}.

Instance MonadTrans_SelectT {r} : MonadTrans (SelectT r) :=
  {| lift _ _ _ u := MkSelectT (fun _ => u)
  |}.

Instance MonadState_SelectT {r s m} `{MonadState s m} : MonadState s (SelectT r m) :=
  {| get := MkSelectT (fun _ => get)
   ; put z := MkSelectT (fun _ => put z)
  |}.

(** ** Simple facts *)

Lemma injective_runSelectT {r m a} (u v : SelectT r m a) :
  runSelectT u = runSelectT v -> u = v.
Proof.
  destruct u, v; cbn; intros []; reflexivity.
Qed.

(** ** Laws *)

Instance LawfulMonad_SelectT {r m} `{LawfulMonad m} : LawfulMonad (SelectT r m).
Proof.
  split; intros; apply injective_runSelectT, functional_extensionality; intros; cbn.
  - rewrite bind_pure_l; reflexivity.
  - rewrite bind_pure_r. f_equal. apply functional_extensionality; intros.
    rewrite bind_pure_l; auto.
  - rewrite bind_assoc. do 2 f_equal. apply functional_extensionality; intros.
    rewrite bind_assoc; auto.
Qed.

Instance LawfulMonadTrans {r} : LawfulMonadTrans (SelectT r).
Proof.
  split; intros; apply injective_runSelectT, functional_extensionality; intros;
  reflexivity.
Qed.

Instance LawfulMonadState {r s m}
  `{LawfulMonad m} `{MonadState s m} {LMS : LawfulMonadState s m} :
  LawfulMonadState s (SelectT r m) :=
  LawfulMonadState_LawfulMonadTrans.
