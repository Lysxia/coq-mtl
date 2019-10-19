(** * Defining monads by retraction *)

(** For example, [ReaderT] and [WriterT] are retracts of [StateT]. *)

From Coq Require Import FunctionalExtensionality.

From mtl.Classes Require Import All.

Implicit Types m n : Type -> Type.

(** A retraction is a left inverse, a section is a right inverse.
    A pair of the two is a semi-isomorphism. *)
Class SemiIso {m n} (retract : forall a, m a -> n a) (section : forall a, n a -> m a) :
  Prop :=
  semi_iso : forall a (u : n a), retract _ (section _ u) = u.

(** Given such a pair, we can convert operations in [m] into operations in [n],
    although that alone is not sufficient to preserve lawfulness. *)

Section MonadRetract.

Context {m n}.
Context (retract : forall a, m a -> n a)
        (section : forall a, n a -> m a).
Context `{SemiIso _ _ retract section}.

(** Convert [Monad m] to a [Monad n] through a semi-isomorphism. *)
Context `{Monad m}.
Instance Monad_Retract : Monad n :=
  {| pure _ x := retract _ (pure x)
   ; bind _ _ u k := retract _ (section _ u >>= fun x => section _ (k x))
  |}.

(** The [section] commutes with [pure] and [bind].
    Note that at this point we don't know whether they're lawful, so it's technically
    not a monad morphism yet. *)
Definition MorphismSection : Prop :=
  @MonadMorphism n m Monad_Retract _ section.

Context `{MorphismSection}.

(** In general, we cannnot simplify [section _ (retract _ t)] to [t]
    (we only have [retract _ (section _ u) = u]).
    However, we can infer most of the laws from a few special cases of this
    equation, which we name [sr] for brevity. *)
Local Notation sr t := (section _ (retract _ t) = t).

(** These equations are reformulations of the [MorphismSection] assumption above,
    for easy rewriting in Coq. *)
Local Lemma section_pure {a} (x : a) : sr (pure x).
Proof. destruct H1; cbn in *; auto. Qed.

Local Lemma section_bind {a b} (u : n a) (k : a -> n b) :
  sr (section _ u >>= fun x => section _ (k x)).
Proof. destruct H1; cbn in *; auto. Qed.

(** Convert a [LawfulMonad m] to a [LawfulMonad n] through a semi-isomorphism
    which satisfies [section_pure] and [section_bind]. *)
Context {LM : LawfulMonad m}.
Instance LawfulMonad_Retract : LawfulMonad n.
Proof.
  split; intros; cbn.
  - rewrite section_pure, bind_pure_l, semi_iso. reflexivity.
  - replace (fun x : a => section _ (retract _ (pure x))) with (@pure m _ a).
    + rewrite bind_pure_r, semi_iso; reflexivity.
    + apply functional_extensionality; intros.
      rewrite section_pure; auto.
  - rewrite section_bind, bind_assoc.
    do 2 f_equal. apply functional_extensionality; intros.
    rewrite section_bind; reflexivity.
Qed.

Section Error.

(** Convert [MonadError e m] to a [MonadError e n] through a semi-isomorphism. *)
Context {e} `{MonadError e m}.
Instance MonadError_Retract : MonadError e n :=
  {| throwError _ err := retract _ (throwError err)
   ; catchError _ u h := retract _ (catchError (section _ u) (fun err => section _ (h err)))
  |}.

(** Again, to prove the laws, one needs to check that the semi-isomorphism is
    well-behaved on the [MonadError] operations. *)
Class MonadErrorMorphismSection : Prop :=
  { section_throwError : forall a err, sr (@throwError _ _ _ a err)
  ; section_catchError : forall a (u : n a) h,
      sr (catchError (section _ u) (fun err => section _ (h err)))
  }.

(** Convert [LawfulMonadError e m] to [LawfulMonadError e n]. *)
Context {EMS : MonadErrorMorphismSection}
        {LME : LawfulMonadError e m}.

Instance LawfulMonadError_Retract : LawfulMonadError e n.
Proof.
  split; intros; cbn.
  - rewrite section_throwError, catch_throw, semi_iso. reflexivity.
  - rewrite section_catchError, catch_catch.
    do 2 f_equal; apply functional_extensionality; intros.
    rewrite section_catchError. reflexivity.
  - rewrite section_pure, catch_pure; reflexivity.
  - replace (fun err => section _ (retract _ (throwError err))) with (throwError : e -> m a).
    + rewrite catch_rethrow, semi_iso; reflexivity.
    + apply functional_extensionality; intros.
      rewrite section_throwError; reflexivity.
  - rewrite section_throwError, left_zero_throw; reflexivity.
  - rewrite section_catchError, section_bind.
    assert (spf : (fun x => section _ (retract _ (pure (f x))))
                = (fun x => pure (f x) : m _)).
    { apply functional_extensionality; intros; rewrite section_pure; reflexivity. }
    rewrite spf at 1 2.
    fold (mapM f (catchError (section _ u) (fun err => section _ (h err)))).
    rewrite natural_catch.
    do 2 f_equal; apply functional_extensionality; intros.
    rewrite section_bind, spf; reflexivity.
Qed.

End Error.

Section State.

(** Convert [MonadState s m] to a [MonadState s n] through a semi-isomorphism. *)
Context {s} `{MonadState s m}.
Instance MonadState_Retract : MonadState s n :=
  {| get := retract _ get
   ; put z := retract _ (put z)
  |}.

(** The semi-isomorphism is well-behaved on the [MonadState] operations. *)
Class MonadStateMorphismSection : Prop :=
  { section_get : sr get
  ; section_put : forall z, sr (put z)
  }.

(** Convert [LawfulMonadState s m] to a [LawfulMonadState s n]. *)
Context {LMS : LawfulMonadState s m}
        {SMS : MonadStateMorphismSection}.

Instance LawfulMonadState_Retract : LawfulMonadState s n.
Proof.
  split; intros; cbn.
  - replace (fun x => section _ (retract _ (put x))) with (@put _ m _).
    + rewrite section_get, get_put; reflexivity.
    + apply functional_extensionality; intros; rewrite section_put; reflexivity.
  - rewrite section_get, section_put, section_pure, put_get; reflexivity.
  - rewrite !section_put, put_put; reflexivity.
Qed.

End State.

End MonadRetract.
