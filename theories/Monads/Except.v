From mtl.Classes Require Import All.

Implicit Types e : Type.
Implicit Types m : Type -> Type.

Record ExceptT e m (a : Type) : Type :=
  MkExceptT { runExceptT : m (e + a)%type }.

Arguments MkExceptT {e m a} _.
Arguments runExceptT {e m a}.

Instance Monad_ExceptT e m `{Monad m} : Monad (ExceptT e m) :=
  {| pure _ x := MkExceptT (pure (inr x))
   ; bind _ _ u k := MkExceptT (
       runExceptT u >>= fun x' =>
       match x' with
       | inl err => pure (inl err)
       | inr x => runExceptT (k x)
       end)
  |}.

Instance MonadTrans_ExceptT e : MonadTrans (ExceptT e) :=
  {| lift _ _ _ u := MkExceptT (u >>= fun x => pure (inr x))
  |}.

