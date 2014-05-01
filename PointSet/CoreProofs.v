(** * Proofs about PointSet.Core *)
Require Export PointSet.Core.

Module Type PointSetProofs (point : Point) (point_set : PointSet point).

  Axiom get_two_points_In : forall (pts : point_set.t 2),
                              point_set.In (fst (point_set.get_two_points pts)) pts
                              /\ point_set.In (snd (point_set.get_two_points pts)) pts.

  Axiom get_two_closest_of_three_In : forall (pts : point_set.t 3),
                                        point_set.In (fst (point_set.get_two_closest_of_three pts)) pts
                                        /\ point_set.In (snd (point_set.get_two_closest_of_three pts)) pts.

  Axiom points_in_strip_In : forall n (pts : point_set.t n)
                                    (median : point.t)
                                    (cur_min_dist : point.distT)
                                    pt,
                               List.In pt (point_set.points_in_strip pts median cur_min_dist)
                               -> point_set.In pt pts.

  Axiom split_In : forall n (pts : point_set.t n) pt,
                     point_set.In pt pts
                     <-> (point_set.In pt (snd (fst (point_set.split pts)))
                          \/ point_set.In pt (snd (point_set.split pts))).
End PointSetProofs.
