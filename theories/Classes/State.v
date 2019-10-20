(** The [MonadState] class *)

(** In this file:
  - The [MonadState] class: [get] and [put].
  - The [state] function, defined in terms of [get] and [put].
    In Haskell mtl, this operation is overridable in [MonadState], but
    it is expected to be equivalent to the default definition.
    The two presentations ([get], [put] vs. [state]) are equivalent,
    see [Monad.State.MonadState'].
  - The [LawfulMonadState] class:
    + [get_put], [put_get], [put_put]
  - Equation derived from those laws:
    + [get_get], [nullipotent_get]
  - Monad transformers can just lift [LawfulMonadState].
 *)

From mtl.Classes Require Import Monad Trans.
From Coq Require Import Setoid FunctionalExtensionality Relations Morphisms.

Implicit Types t : (Type -> Type) -> (Type -> Type).
Implicit Types m : Type -> Type.
Implicit Types s : Type.

Generalizable Variables z.

Class MonadState s m : Type :=
  { get : m s
  ; put : s -> m unit
  }.

Definition state {s m} `{Monad m} `{MonadState s m} {a} : (s -> (a * s)) -> m a :=
  fun f =>
    get >>= fun z0 =>
    let '(x, z) := f z0 in
    put z >>
    pure x.

Class LawfulMonadState s m `{Monad m} `{MonadState s m} : Prop :=
  { get_put :   get    >>= put   = pure tt
  ; put_get : `(put z  >> get    = put z >> pure z)
  ; put_put : `(put z1 >> put z2 = put z2)
  }.

Section StateFacts.

Context s m.
Context `{Monad m} `{MonadState s m}.
Context {LM : LawfulMonad m}.
Context {LMS : LawfulMonadState s m}.

Lemma get_get_pure
  : (get >>= fun z1 => get >>= fun z2 => pure (z1, z2))
  = (get >>= fun z => pure (z, z)).
Proof.
  - transitivity (get >>= fun z0 => put z0 >>= fun _ => get >>= fun z => pure (z, z)).
    + rewrite <- (bind_pure_l _ _ tt (fun _ => _)).
      rewrite <- get_put.
      rewrite bind_assoc.
      f_equal; apply functional_extensionality; intros z1.
      rewrite <- bind_assoc, put_get, bind_assoc.
      transitivity (put z1 >> (get >>= fun z2 => pure (z1, z2))).
      * f_equal; apply functional_extensionality; intros _.
        rewrite bind_pure_l. reflexivity.
      * rewrite <- 2 bind_assoc, put_get, 2 bind_assoc, 2 bind_pure_l.
        reflexivity.
    + rewrite <- bind_assoc, get_put, bind_pure_l.
      reflexivity.
Qed.

(** Variants of [get_get] and [nullipotent_get] which quantify over the final
    continuation. They are equivalent, but a bit less convenient to prove directly
    when lifting [MonadState] through transformers.
  *)

Lemma get_get : forall a (k : s -> s -> m a),
    (get >>= fun z1 => get >>= fun z2 => k z1 z2)
  = (get >>= fun z => k z z).
Proof.
  intros.
  transitivity ((get >>= fun z => pure (z, z)) >>= fun '(z1, z2) => k z1 z2).
  - rewrite <- get_get_pure.
    repeat (rewrite bind_assoc; f_equal; apply functional_extensionality; intros).
    rewrite bind_pure_l; reflexivity.
  - rewrite bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l; reflexivity.
Qed.

(** [get] has no side effect. *)
Lemma nullipotent_get : get >> pure tt = pure tt.
Proof.
  rewrite <- get_put, get_get.
  reflexivity.
Qed.

Lemma nullipotent_get_k : forall a (u : m a),
  get >> u = u.
Proof.
  intros.
  transitivity (get >> pure tt >> u).
  - rewrite bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l; reflexivity.
  - rewrite nullipotent_get, bind_pure_l; reflexivity.
Qed.

Lemma get_state : get = state (fun z => (z, z)).
Proof.
  unfold state.
  replace (fun _ => _) with (fun z0 => put z0 >> get).
  2: apply functional_extensionality; apply put_get.
  rewrite <- bind_assoc, get_put, bind_pure_l.
  reflexivity.
Qed.

Lemma put_state : `(put z = state (fun _ => (tt, z))).
Proof.
  intros; unfold state.
  rewrite nullipotent_get_k.
  replace (fun _ => pure tt) with (fun t : unit => pure t).
  2: apply functional_extensionality; intros []; auto.
  rewrite bind_pure_r.
  reflexivity.
Qed.

End StateFacts.

Definition MonadState_MonadTrans {s t m} `{MonadTrans t} `{Monad m} `{MonadState s m} :
  MonadState s (t m) :=
  {| get := lift get
   ; put z := lift (put z)
  |}.

Theorem LawfulMonadState_LawfulMonadTrans {s t m}
  `{LawfulMonadTrans t}
  `{LawfulMonad m}
  `{MonadState s m}
  {_ : LawfulMonadState s m} :
  @LawfulMonadState s (t m) _ MonadState_MonadTrans.
Proof.
  split; cbn; intros; rewrite <- ?morphism_bind.
  - rewrite get_put, morphism_pure; reflexivity.
  - rewrite put_get, morphism_bind; f_equal;
    apply functional_extensionality; intros; apply morphism_pure.
  - rewrite put_put; reflexivity.
Qed.
