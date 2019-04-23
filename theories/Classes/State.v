From mtl.Classes Require Import Monad.
From Coq Require Import Setoid FunctionalExtensionality Relations Morphisms.

Instance sss {a b} : subrelation (eq ==> eq)%signature (@eq (a -> b)).
Proof.
Admitted.

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
  ; get_get : forall a (k : s -> s -> m a),
      (get >>= fun z1 => get >>= fun z2 => k z1 z2) = (get >>= fun z => k z z)
    (* [get] has no side effect. *)
  ; nullipotent_get : forall a (u : m a), get >> u = u
  }.

Section StateFacts.

Context s m.
Context `{Monad m} `{MonadState s m}.
Context {LM : LawfulMonad m}.
Context {LMS : LawfulMonadState s m}.

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
  rewrite nullipotent_get.
  replace (fun _ => pure tt) with (fun t : unit => pure t).
  2: apply functional_extensionality; intros []; auto.
  rewrite bind_pure_r.
  reflexivity.
Qed.

End StateFacts.
