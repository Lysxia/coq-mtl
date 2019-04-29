(** * The writer monad transformer *)

From Coq Require Import List FunctionalExtensionality.
Import ListNotations.
From mtl.Classes Require Import All.

Implicit Types w a b : Type.
Implicit Types m : Type -> Type.

(** ** Monoids *)

Class Monoid w : Type :=
  { mempty : w
  ; mappend : w -> w -> w
  }.

Arguments mempty {w _}.
Arguments mappend {w _}.

Delimit Scope monoid_scope with monoid.

Infix "++" := mappend : monoid_scope.

Class LawfulMonoid w `{Monoid w} : Type :=
  { mappend_mempty_l : forall r, mappend mempty r = r
  ; mappend_mempty_r : forall r, mappend r mempty = r
  ; mappend_assoc : forall r s t, mappend (mappend r s) t = mappend r (mappend s t)
  }.

(** *** List monoid *)

Instance Monoid_list {a} : Monoid (list a) :=
  {| mempty := []
   ; mappend := @app _
  |}.

Instance LawfulMonoid_list {a} : LawfulMonoid (list a).
Proof.
  split; intros.
  - auto.
  - apply app_nil_r.
  - symmetry; apply app_assoc.
Qed.

(** ** Writer transformer *)

Record WriterT w m a : Type :=
  MkWriterT { runWriterT : m (w * a)%type }.

Arguments MkWriterT {w m a} _.
Arguments runWriterT {w m a} _.

(** ** Instances *)

Instance Monad_WriterT {w} `{Monoid w} {m} `{Monad m} : Monad (WriterT w m) :=
  {| pure _ x := MkWriterT (pure (mempty, x))
   ; bind _ _ u k := MkWriterT (
       runWriterT u >>= fun '(r, x) =>
       runWriterT (k x) >>= fun '(s, y) =>
       pure (r ++ s, y)%monoid)
  |}.

Instance MonadTrans_WriterT {w} `{Monoid w} : MonadTrans (WriterT w) :=
  {| lift _ _ _ u := MkWriterT (u >>= fun x => pure (mempty, x))
  |}.

Instance MonadState_WriterT {w} `{Monoid w} {s m} `{Monad m} `{MonadState s m} :
  MonadState s (WriterT w m) :=
  MonadState_MonadTrans.

Instance MonadError_WriterT {w} `{Monoid w} {e m} `{Monad m} `{MonadError e m} :
  MonadError e (WriterT w m) :=
  {| throwError _ err := MkWriterT (throwError err)
   ; catchError _ u h := MkWriterT (
       catchError (runWriterT u) (fun err => runWriterT (h err)))
  |}.

(** ** Simple facts *)

Lemma injective_runWriterT {w m a} (u v : WriterT w m a) :
  runWriterT u = runWriterT v -> u = v.
Proof.
  destruct u, v; simpl; intros []; auto.
Qed.

(** ** Laws *)

Section Laws.

Context {w} `{LawfulMonoid w}.

Instance LawfulMonad_WriterT {m} `{LawfulMonad m} :
  LawfulMonad (WriterT w m).
Proof.
  split; intros; apply injective_runWriterT; cbn; auto.
  - rewrite bind_pure_l.
    transitivity (runWriterT (k x) >>= pure).
    + f_equal; apply functional_extensionality; intros [].
      rewrite mappend_mempty_l. reflexivity.
    + rewrite bind_pure_r; reflexivity.
  - transitivity (runWriterT u >>= pure).
    + f_equal; apply functional_extensionality; intros [].
      rewrite bind_pure_l, mappend_mempty_r. reflexivity.
    + rewrite bind_pure_r; reflexivity.
  - do 3 (rewrite !bind_assoc; f_equal; apply functional_extensionality; intros [];
      try rewrite bind_pure_l).
    rewrite mappend_assoc; reflexivity.
Qed.

Instance LawfulMonadTrans_WriterT : LawfulMonadTrans (WriterT w).
Proof.
  split; intros; apply injective_runWriterT; cbn; auto.
  - rewrite bind_pure_l; reflexivity.
  - do 2 (rewrite !bind_assoc; f_equal; apply functional_extensionality; intros;
      try rewrite bind_pure_l).
    rewrite mappend_mempty_l; reflexivity.
Qed.

Instance LawfulMonadState_WriterT {s m}
  `{LawfulMonad m} `{MonadState s m} {LMS : LawfulMonadState s m} :
  LawfulMonadState s (WriterT w m) :=
  LawfulMonadState_LawfulMonadTrans.

Instance LawfulMonadError_WriterT {e m}
  `{LawfulMonad m} `{MonadError e m} {LME : LawfulMonadError e m} :
  LawfulMonadError e (WriterT w m).
Proof.
  destruct LME.
  split; intros; apply injective_runWriterT; cbn; intros; auto.
  - rewrite catch_throw; reflexivity.
  - replace (fun '(r, x) => pure (mempty, f x) >>= fun '(s, y) => pure ((r ++ s)%monoid, y))
      with (fun rx : w * a => pure (fst rx, f (snd rx))).
    + fold (mapM (fun rx => (fst rx, f (snd rx))) (catchError (runWriterT u) (fun err => runWriterT (h err)))).
      rewrite natural_catch. reflexivity.
    + apply functional_extensionality; intros []; rewrite bind_pure_l.
      rewrite mappend_mempty_r; reflexivity.
Qed.
