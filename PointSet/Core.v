(** * A set of points *)
Require Export Div2.
Require Export Point.Core.

Module Type PointSet (point : Point).
  Axiom t : nat -> Type.
  Axiom split_marker : Type.

  (** Returns the median, points to the left of the median, and points to the right of the median. *)
  Axiom split : forall n,
                  t n
                  -> (point.t + {n = 0}) * (*split_marker * *) t (div2 n) * t (n - (div2 n)).
  Axiom points_sets_in_strip : forall n,
                                 t n
                                 -> point.distT
                                 -> list (point.t * { x : nat & t x }).
  Axiom points_in_strip : forall n,
                            t n
                            -> forall (median : point.t)
                                      (cur_min_dist : point.distT),
                                 list point.t.

  Axiom Forall : forall (P : point.t -> Prop) n, t n -> Prop.
  Axiom In : forall (x : point.t) n, t n -> Prop.

  Axiom get_two_points : t 2 -> point.t * point.t.
  (*Axiom get_two_points_dist : t 2 -> point.distT.*)
  (*Axiom get_three_points_min_dist : t 3 -> point.distT.*)
  Axiom get_two_closest_of_three : t 3 -> point.t * point.t.
End PointSet.
