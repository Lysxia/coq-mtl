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

(** [State] is equivalent to [s -> (a * s)] *)
Definition runState {s a} (u : State s a) : s -> a * s :=
  fun z => runIdentity (runStateT u z).

Definition MkState {s a} (f : s -> a * s) : State s a :=
  MkStateT (fun z => MkIdentity (f z)).

Lemma runState_mono {s a} (u : State s a) : MkState (runState u) = u.
Proof.
  apply injective_runStateT, functional_extensionality.
  intros; apply injective_runIdentity; auto.
Qed.

Lemma MkState_mono {s a} (f : s -> a * s) : runState (MkState f) = f.
Proof.
  reflexivity.
Qed.

Lemma MkState_state {s a} (f : s -> a * s)
  : MkState f = state f.
Proof.
  unfold MkState; cbn.
  f_equal; apply functional_extensionality; intros.
  destruct f; reflexivity.
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

Definition first {a a' b} (f : a -> a') (p : a * b) : a' * b :=
  let '(x, y) := p in
  (f x, y).

Lemma mapM_first {m} `{Monad m} {a a' b} (f : a -> a') (u : m (a * b)%type) :
  (u >>= fun '(x, y) => pure (f x, y)) = (mapM (first f) u).
Proof.
  unfold mapM; f_equal; apply functional_extensionality; intros []; reflexivity.
Qed.

Instance LawfulMonadError_StateT {e s m}
  `{LawfulMonad m} {ME : MonadError e m} {LME : LawfulMonadError e m} :
  LawfulMonadError e (StateT s m).
Proof.
  destruct LME.
  split; intros; cbn; apply injective_runStateT, functional_extensionality;
    cbn; intros; auto.
  - apply catch_throw.
  - rewrite mapM_first, natural_catch.
    f_equal.
    + rewrite <- mapM_first; reflexivity.
    + apply functional_extensionality; intros; rewrite <- mapM_first; reflexivity.
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
  - transitivity (catchError (runStateT u x) throwError).
    + f_equal; apply functional_extensionality; intros []; auto.
    + auto.
  - rewrite mapM_first, natural_catch.
    f_equal.
    + rewrite <- mapM_first; reflexivity.
    + apply functional_extensionality; intros []; rewrite <- mapM_first; reflexivity.
Qed.

Theorem CatchBind_StateT_recoverable {e s m}
  `{LawfulMonad m} {ME : MonadError (e * s) m} {LME : LawfulMonadError (e * s) m}
  {CB_m : CatchBind (e * s) m} :
  @CatchBind e (StateT s m) _ MonadError_StateT_recoverable.
Proof.
  red; intros; apply injective_runStateT, functional_extensionality;
    cbn; intros.
  rewrite 2 CB_m. unfold tryError.
  rewrite !bind_assoc.
  f_equal.
  apply functional_extensionality; intros [ [] | []]; cbn.
  + rewrite bind_pure_l; reflexivity.
  + rewrite catch_pure, bind_pure_l; reflexivity.
Qed.

(** ** Completeness *)
(** We give a second characterization of "lawful instances" and show they
    are equivalent. *)

Class MonadState' s m : Type :=
  state' : forall a, State s a -> m a.

Arguments state' {s m _} [a].

Class LawfulMonadState' s m `{Monad m} `{MonadState' s m} : Type :=
  state'_morphism :> MonadMorphism (State s) m state'.

Section Completeness.

(** [MonadState] and [MonadState'] instances can be defined in terms of each other. *)

(** Using [get] and [put] from the pure [State] monad. *)
Instance MonadState_MonadState' {s m} `{MonadState' s m} : MonadState s m | 9 :=
  {| get := state' get
   ; put z := state' (put z)
  |}.

Instance MonadState'_MonadState {s m} `{Monad m} `{MonadState s m} : MonadState' s m | 9 :=
  fun _ u => state (runState u).

(** The two definitions are inverses of each other. *)

Lemma MS_MS'_MS {s m} `{LawfulMonad m} {MS : MonadState s m} {_ : LawfulMonadState s m}
  : @MonadState_MonadState' _ _ _ = MS.
Proof.
  destruct MS. unfold MonadState_MonadState', MonadState'_MonadState, state'; cbn.
  f_equal.
  - rewrite <- get_state; auto.
  - apply functional_extensionality; intros. unfold runState; cbn.
    rewrite <- put_state; auto.
Qed.

Lemma MS'_MS_MS' {s m} `{Monad m} {MS' : MonadState' s m} {_ : LawfulMonadState' s m}
  : @MonadState'_MonadState _ _ _ _ = MS'.
Proof.
  unfold MonadState_MonadState', MonadState'_MonadState; cbn.
  apply functional_extensionality_dep; intros a.
  apply functional_extensionality; intros u.
  replace (MS' a u) with (state' u); try reflexivity.
  replace u with (state (runState u) : State s a) at 2.
  - unfold state at 2.
    rewrite morphism_bind.
    unfold state.
    f_equal; try reflexivity.
    apply functional_extensionality; intros z.
    destruct runState.
    rewrite morphism_bind.
    f_equal; try reflexivity.
    apply functional_extensionality; intros; rewrite morphism_pure.
    reflexivity.
  - apply injective_runStateT, functional_extensionality; intros; cbn.
    unfold runState.
    destruct (runStateT u) as [[]].
    reflexivity.
Qed.

(** And the laws imply each other. *)

Theorem LawfulMonadState'_LawfulMonadState {s m}
  `{LawfulMonad m} `{MonadState s m} {LMS : LawfulMonadState s m}
  : LawfulMonadState' s m.
Proof.
  split; intros; unfold state', MonadState'_MonadState, state; cbn.
  - rewrite <- bind_assoc, get_put, bind_pure_l. reflexivity.
  - rewrite bind_assoc. f_equal. apply functional_extensionality; intros; cbn.
    unfold runState; cbn.
    destruct (runStateT u x) as [[]]; cbn.
    rewrite bind_assoc, bind_pure_l, <- bind_assoc, put_get, bind_assoc, bind_pure_l.
    destruct runStateT as [[]]; cbn.
    rewrite <- bind_assoc, put_put.
    reflexivity.
Qed.

Theorem LawfulMonadState_LawfulMonadState' {s m}
  `{LawfulMonad m} `{MonadState' s m} {LMS' : LawfulMonadState' s m}
  : LawfulMonadState s m.
Proof.
  split; intros; cbn.
  all: try rewrite <- morphism_pure; try rewrite <- morphism_bind.
  all: try reflexivity.
  - rewrite <- (morphism_bind _ _ _ (fun _ => pure z)).
    reflexivity.
  - transitivity (state' (get >>= fun z1 => get >>= fun z2 => pure (z1, z2))).
    + rewrite morphism_bind.
      f_equal. apply functional_extensionality; intros.
      rewrite morphism_bind.
      f_equal. apply functional_extensionality; intros.
      rewrite morphism_pure.
      reflexivity.
    + rewrite get_get.
      rewrite morphism_bind.
      f_equal. apply functional_extensionality; intros.
      rewrite morphism_pure.
      reflexivity.
Qed.

End Completeness.
