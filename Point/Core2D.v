Require Export Point.Core.

Module Type Point2D <: Point.
  Include Point.
  Axiom y_le : t -> t -> Prop.
  Axiom y_le_dec : forall x y, {y_le x y} + {~y_le x y}.
End Point2D.
