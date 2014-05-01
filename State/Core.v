Require Export Point.Core PointSet.Core.

Module State (point : Point) (point_set : PointSet point).
  Record State :=
    {
      closest_points : point.t * point.t;
      min_dist := point.get_dist (fst closest_points) (snd closest_points);
      left_points : { n : _ & point_set.t n };
      median : point.t;
      right_points : { n : _ & point_set.t n };
      center_points : list point.t;
      closest_left_points : point.t * point.t;
      closest_right_points : point.t * point.t;
      closest_center_points : point.t * point.t
    }.
End State.
