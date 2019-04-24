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
  ; get_get :
        (get >>= fun z1 => get >>= fun z2 => pure (z1, z2))
      = (get >>= fun z => pure (z, z))
    (* [get] has no side effect. *)
  ; nullipotent_get : get >> pure tt = pure tt
  }.

Section StateFacts.

Context s m.
Context `{Monad m} `{MonadState s m}.
Context {LM : LawfulMonad m}.
Context {LMS : LawfulMonadState s m}.

(** Variants of [get_get] and [nullipotent_get] which quantify over the final
    continuation. They are equivalent, but a bit less convenient to prove directly
    when lifting [MonadState] through transformers.
  *)

Lemma get_get_k : forall a (k : s -> s -> m a),
    (get >>= fun z1 => get >>= fun z2 => k z1 z2)
  = (get >>= fun z => k z z).
Proof.
  intros.
  transitivity ((get >>= fun z => pure (z, z)) >>= fun '(z1, z2) => k z1 z2).
  - rewrite <- get_get.
    repeat (rewrite bind_assoc; f_equal; apply functional_extensionality; intros).
    rewrite bind_pure_l; reflexivity.
  - rewrite bind_assoc; f_equal; apply functional_extensionality; intros.
    rewrite bind_pure_l; reflexivity.
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
  `{MonadTrans t}
  `{forall m, Monad m -> Monad (t m)}
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
  - transitivity (lift (get >>= fun z => pure (z, z))).
    + rewrite <- get_get.
      do 2 (rewrite morphism_bind; f_equal; apply functional_extensionality; intros).
      rewrite morphism_pure; reflexivity.
    + rewrite morphism_bind; f_equal; apply functional_extensionality; intros.
      rewrite morphism_pure; reflexivity.
  - transitivity (lift (get >> pure tt)).
    + rewrite morphism_bind; f_equal; apply functional_extensionality; intros.
      rewrite morphism_pure; reflexivity.
    + rewrite nullipotent_get, morphism_pure; reflexivity.
Qed.
