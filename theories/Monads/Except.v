(** * The exception monad transformer *)

(** In this file:
  - The [ExceptT] monad transformer.
  - Instances:
    + [Monad], [LawfulMonad]
    + [MonadTrans], [LawfulMonadTrans]
    + [MonadState], [LawfulMonadState] (derivable for all transformers)
    + [MonadError], [LawfulMonadError], and [CatchBind]
 *)

From Coq Require Import FunctionalExtensionality.
From mtl.Classes Require Import All.

Implicit Types e : Type.
Implicit Types m : Type -> Type.

Record ExceptT e m (a : Type) : Type :=
  MkExceptT { runExceptT : m (e + a)%type }.

Arguments MkExceptT {e m a} _.
Arguments runExceptT {e m a}.

(** ** Instances *)

Instance Monad_ExceptT {e m} `{Monad m} : Monad (ExceptT e m) :=
  {| pure _ x := MkExceptT (pure (inr x))
   ; bind _ _ u k := MkExceptT (
       runExceptT u >>= fun x' =>
       match x' with
       | inl err => pure (inl err)
       | inr x => runExceptT (k x)
       end)
  |}.

Instance MonadTrans_ExceptT {e} : MonadTrans (ExceptT e) :=
  {| lift _ _ _ u := MkExceptT (u >>= fun x => pure (inr x))
  |}.

Instance MonadState_ExceptT {e s m} `{Monad m} `{MonadState s m} :
  MonadState s (ExceptT e m) :=
  MonadState_MonadTrans.

Instance MonadReader_ExceptT {e r m} `{Monad m} `{MonadReader r m} :
  MonadReader r (ExceptT e m) :=
  {| ask := MkExceptT (ask >>= fun x => pure (inr x))
   ; local := fun f _ u => MkExceptT (local f (runExceptT u))
  |}.

Instance MonadError_ExceptT {e m} `{Monad m} : MonadError e (ExceptT e m) :=
  {| throwError _ err := MkExceptT (pure (inl err))
   ; catchError _ u h := MkExceptT (runExceptT u >>= fun x' =>
       match x' with
       | inl err => runExceptT (h err)
       | inr x => pure (inr x)
       end)
  |}.

(** ** Simple facts *)

Lemma injective_runExceptT {e m a} (u v : ExceptT e m a) :
  runExceptT u = runExceptT v -> u = v.
Proof.
  destruct u, v; intros; f_equal; auto.
Qed.

(** ** Laws *)

Instance LawfulMonad_ExceptT {e m} `{LawfulMonad m} : LawfulMonad (ExceptT e m).
Proof.
  split.
  all: intros; apply injective_runExceptT; cbn.
  - rewrite bind_pure_l. reflexivity.
  - transitivity (runExceptT u >>= pure).
    + f_equal; apply functional_extensionality; intros []; auto.
    + rewrite bind_pure_r. reflexivity.
  - rewrite bind_assoc; f_equal; apply functional_extensionality; intros []; auto.
    rewrite bind_pure_l; reflexivity.
Qed.

Instance LawfulMonadTrans_ExceptT {e} : LawfulMonadTrans (ExceptT e).
Proof.
  split; intros; cbn.
  - rewrite bind_pure_l; reflexivity.
  - rewrite !bind_assoc; do 2 f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l; reflexivity.
Qed.

Instance LawfulMonadState_ExceptT {e s m} `{LawfulMonad m} `{MonadState s m}
  {_ : LawfulMonadState s m} : LawfulMonadState s (ExceptT e m) :=
  LawfulMonadState_LawfulMonadTrans.

Instance LawfulMonadReader_ExceptT {e r m} `{LawfulMonad m} `{MonadReader r m}
  {_ : LawfulMonadReader r m} : LawfulMonadReader r (ExceptT e m).
Proof.
  repeat split; intros; apply injective_runExceptT; cbn.
  all: repeat srewrite bind_pure_bind.
  - setoid_rewrite <- ask_comm_k.
    unbind; intros [].
    + rewrite ask_nullipotent; reflexivity.
    + srewrite bind_pure_bind; reflexivity.
  - apply ask_nullipotent.
  - apply ask_ask_k.
  - rewrite morphism_bind, local_ask, bind_pure_bind. srewrite morphism_pure.
    reflexivity.
  - apply local_const.
  - apply local_id.
  - apply local_local.
  - apply morphism_pure.
  - rewrite morphism_bind. unbind; intros [].
    + apply morphism_pure.
    + reflexivity.
Qed.

Instance LawfulMonadError_ExceptT {e m} `{LawfulMonad m} : LawfulMonadError e (ExceptT e m).
Proof.
  split; intros; apply injective_runExceptT; cbn.
  all: try (rewrite bind_pure_l; reflexivity).
  - rewrite bind_assoc. f_equal; apply functional_extensionality; intros [].
    + reflexivity.
    + rewrite bind_pure_l. reflexivity.
  - transitivity (runExceptT u >>= pure).
    + f_equal; apply functional_extensionality; intros []; auto.
    + rewrite bind_pure_r; reflexivity.
  - rewrite !bind_assoc; f_equal; apply functional_extensionality; intros [];
      rewrite !bind_pure_l.
    + f_equal; apply functional_extensionality; intros; reflexivity.
    + reflexivity.
Qed.

Theorem CatchBind_ExceptT {e m} `{LawfulMonad m} : CatchBind e (ExceptT e m).
Proof.
  red; intros; apply injective_runExceptT; cbn.
  rewrite !bind_assoc. f_equal; apply functional_extensionality; intros [];
    rewrite !bind_pure_l; reflexivity.
Qed.
