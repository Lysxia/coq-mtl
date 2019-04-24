(** * Exception effect *)

From mtl.Classes Require Import Monad Trans.

Implicit Types e : Type.
Implicit Types m : Type -> Type.

Class MonadError e m : Type :=
  { throwError : forall a, e -> m a
  ; catchError : forall a, m a -> (e -> m a) -> m a
  }.

Arguments throwError {e m _ a}.
Arguments catchError {e m _ a}.

Definition tryError {e m} `{Monad m} `{MonadError e m} {a} : m a -> m (e + a)%type :=
  fun u =>
    catchError (u >>= fun x => pure (inr x)) (fun err => pure (inl err)).

Definition either {a b c} (f : a -> c) (g : b -> c) : a + b -> c :=
  fun t =>
    match t with
    | inl x => f x
    | inr y => g y
    end.

Class LawfulMonadError e m `{Monad m} `{MonadError e m} : Prop :=
  { catch_throw : forall err a (h : e -> m a),
      catchError (throwError err) h = h err
  ; catch_catch : forall a (u : m a) (k h : e -> m a),
      catchError (catchError u k) h = catchError u (fun err => catchError (k err) h)
  ; catch_pure : forall a (x : a) h,
      catchError (pure x) h = pure x

  ; catch_rethrow : forall a (u : m a),
      catchError u throwError = u
  ; left_zero_throw : forall err a b (k : a -> m b),
      throwError err >>= k = throwError err
  }.

(** Although it looks nice, the following law is broken by [StateT]. *)
Definition CatchBind e m `{Monad m} `{MonadError e m} : Prop :=
  forall a b (u : m a) (k : a -> m b) h,
      catchError (u >>= k) h = tryError u >>= either h (fun x => catchError (k x) h).
