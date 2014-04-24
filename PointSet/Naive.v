(** * Naïve Point Set *)
Require Export Vector.
Require Export Point.Core PointSet.Core SplitMarker.Core VectorQuickSelect.

Module NaivePointSet (point : Point) (splitter : SplitMarker point) <: PointSet point.
  Definition t := Vector.t point.t.
  Definition split_marker := splitter.t.

  Definition split : forall n,
                       t n
                       -> split_marker * t (div2 n) * t (n - (div2 n))
    := fun n =>
         match n as n return t n -> _ * t (div2 n) * t (n - div2 n) with
           | 0 => fun _ => (splitter.make_split_marker List.nil None List.nil, Vector.nil _, Vector.nil _)
           | S n' => fun all_points =>
                       let split_pts := @vector_quick_select
                                          _
                                          point.x_le point.x_le_dec
                                          (div2 (S n'))
                                          (S n')
                                          (lt_div2 _ (lt_0_Sn _))
                                          all_points in
                       let median := fst (fst split_pts) in
                       let left_tree := snd (fst split_pts) in
                       let right_tree := snd split_pts in
                       match median with
                         | inright pf => match Nat.neq_succ_0 _ pf with end
                         | inleft median_v =>
                           (splitter.make_split_marker
                              (Vector.to_list left_tree)
                              (Some median_v)
                              (Vector.to_list right_tree),
                            left_tree,
                            right_tree)
                       end
         end.

  Fixpoint points_sets_in_strip n (pts : t n) (max_dist : point.distT) {struct pts}
  : list (point.t * { x : nat & t x })
    := match pts with
         | Vector.nil => List.nil
         | Vector.cons x _ xs =>
           (x, take_while (fun y => point.point_in_strip_close_enough x max_dist y)
                          xs)
             ::points_sets_in_strip xs max_dist
       end.


  Definition get_two_points_dist : t 2 -> point.distT.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    exact (point.get_dist x y).
  Defined.

  Definition get_three_points_min_dist : t 3 -> point.distT.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    inversion_clear v as [|z ? v']; rename v' into v.
    exact (point.min_dist (point.min_dist (point.get_dist x y) (point.get_dist y z)) (point.get_dist x z)).
  Defined.
End NaivePointSet.
