(** * A set of points *)
Require Export Div2.
Require Export Point.Core.

Module Type PointSet (point : Point).
  Axiom t : nat -> Type.
  Axiom split_marker : Type.

  Axiom split : forall n,
                  t n
                  -> split_marker * t (div2 n) * t (n - (div2 n)).
  Axiom points_sets_in_strip : forall n,
                                 t n
                                 -> point.distT
                                 -> list (point.t * { x : nat & t x }).

  Axiom get_two_points_dist : t 2 -> point.distT.
  Axiom get_three_points_min_dist : t 3 -> point.distT.
End PointSet.
