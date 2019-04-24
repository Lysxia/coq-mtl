(** * The state monad transformer *)

From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All.
From mtl.Monads Require Import Identity.

Implicit Types s : Type.
Implicit Types m n : Type -> Type.

Record StateT s m (a : Type) : Type :=
  MkStateT { runStateT : s -> m (a * s)%type }.

Arguments MkStateT {s m a} _.
Arguments runStateT {s m a} _.

Definition State s : Type -> Type := StateT s Identity.

(** ** Instances *)

Instance Monad_StateT {s m} `{Monad m} : Monad (StateT s m) :=
  {| pure _ x := MkStateT (fun z => pure (x, z))
   ; bind _ _ u k := MkStateT (fun z =>
     runStateT u z >>= fun '(x, z1) =>
     runStateT (k x) z1)
  |}.

Instance MonadTrans_StateT {s} : MonadTrans (StateT s) :=
  {| lift _ _ _ u := MkStateT (fun z => u >>= fun x => pure (x, z))
  |}.

Instance MonadState_StateT {s m} `{Monad m} : MonadState s (StateT s m) :=
  {| get := MkStateT (fun z => pure (z, z))
   ; put z := MkStateT (fun _ => pure (tt, z))
  |}.

Instance MonadError_StateT {e s m} `{Monad m} `{MonadError e m} :
  MonadError e (StateT s m) :=
  {| throwError _ err := MkStateT (fun _ => throwError err)
   ; catchError _ u h := MkStateT (fun z =>
       catchError (runStateT u z) (fun err => runStateT (h err) z))
  |}.

(** Interestingly, there is another lawful instance of [MonadError] for [MonadState],
    which relies on the ability to throw an exception together with the current state. *)
Definition MonadError_StateT_recoverable {e s m} `{Monad m} `{MonadError (e * s) m} :
  MonadError e (StateT s m) :=
  {| throwError _ err := MkStateT (fun z => throwError (err, z))
   ; catchError _ u h := MkStateT (fun z =>
       catchError (runStateT u z) (fun '(err, z') => runStateT (h err) z'))
  |}.

(** ** Simple facts *)

Lemma injective_runStateT {s m a} (u v : StateT s m a) :
  runStateT u = runStateT v -> u = v.
Proof.
  destruct u, v; intros; f_equal; auto.
Qed.

(** ** Laws *)

Instance LawfulMonad_StateT {s m} `{LawfulMonad m} : LawfulMonad (StateT s m).
Proof.
  split.
  all: intros; apply injective_runStateT, functional_extensionality; intros; cbn.
  - rewrite bind_pure_l. reflexivity.
  - replace (fun _ => _) with (fun z : a * s => pure z).
    2: apply functional_extensionality; intros []; auto.
    rewrite bind_pure_r. reflexivity.
  - rewrite bind_assoc.
    f_equal. apply functional_extensionality. intros []. reflexivity.
Qed.

Instance LawfulMonadTrans_StateT {s m} : LawfulMonadTrans (StateT s).
Proof.
  split.
  all: intros; cbn; f_equal; apply functional_extensionality; intros.
  - rewrite bind_pure_l; reflexivity.
  - rewrite 2 bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l. reflexivity.
Qed.

Instance LawfulMonadState_StateT {s m} `{LawfulMonad m} : LawfulMonadState s (StateT s m).
Proof.
  split.
  all: intros; cbn; apply injective_runStateT, functional_extensionality; cbn; intros.
  all: rewrite ?bind_pure_l; try reflexivity.
Qed.

Instance LawfulMonadError_StateT {e s m}
  `{LawfulMonad m} {ME : MonadError e m} {LME : LawfulMonadError e m} :
  LawfulMonadError e (StateT s m).
Proof.
  destruct LME.
  split; intros; cbn; apply injective_runStateT, functional_extensionality;
    cbn; intros; auto.
  - apply catch_throw.
  - rewrite 2 catch_bind. unfold tryError.
    rewrite !bind_assoc.
    f_equal.
    apply functional_extensionality; intros [ | []]; cbn.
    all: rewrite bind_pure_l; reflexivity.
Qed.

Theorem LawfulMonadError_StateT_recoverable {e s m}
  `{LawfulMonad m} {ME : MonadError (e * s) m} {LME : LawfulMonadError (e * s) m} :
  @LawfulMonadError e (StateT s m) _ MonadError_StateT_recoverable.
Proof.
  destruct LME.
  split; intros; cbn; apply injective_runStateT, functional_extensionality;
    cbn; intros; auto.
  - apply catch_throw.
  - rewrite catch_catch. f_equal. apply functional_extensionality; intros [].
    reflexivity.
  - rewrite 2 catch_bind. unfold tryError.
    rewrite !bind_assoc.
    f_equal.
    apply functional_extensionality; intros [ [] | []]; cbn.
    all: rewrite bind_pure_l; reflexivity.
  - transitivity (catchError (runStateT u x) throwError).
    + f_equal; apply functional_extensionality; intros []; auto.
    + auto.
Qed.
