From Coq Require Export Setoid Morphisms FunctionalExtensionality.

Notation pw := (pointwise_relation _).

Ltac srewrite1 i := setoid_rewrite i.

Ltac srewrite f :=
  lazymatch f with
  | (?w, ?i) => srewrite w; srewrite1 i
  | _ => srewrite1 f
  end.
