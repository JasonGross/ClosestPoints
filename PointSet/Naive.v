(** * Naïve Point Set *)
Require Export Vector.
Require Export Point.Core PointSet.Core SplitMarker.Core VectorQuickSelect.

Module NaivePointSet (point : Point) (splitter : SplitMarker point) <: PointSet point.
  Definition t := Vector.t point.t.
  Definition split_marker := splitter.t.

  Definition Forall : forall (P : point.t -> Prop) n, t n -> Prop
    := @Vector.Forall point.t.
  Definition In : forall (x : point.t) n, t n -> Prop
    := @Vector.In point.t.

  Definition split : forall n,
                       t n
                       -> (point.t + {n = 0}) * (*split_marker * *) t (div2 n) * t (n - (div2 n))
    := fun n =>
         match n as n return t n -> _ * t (div2 n) * t (n - div2 n) with
           | 0 => fun _ => (inright eq_refl, (*splitter.make_split_marker List.nil None List.nil,*) Vector.nil _, Vector.nil _)
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
                           (inleft median_v,
                            (*splitter.make_split_marker
                              (Vector.to_list left_tree)
                              (Some median_v)
                              (Vector.to_list right_tree),*)
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

  Local Open Scope vector_scope.
  Program Definition get_two_points : t 2 -> point.t * point.t
    := fun v
       => match v in Vector.t _ n return n = 2 -> _ with
            | [] => fun H => !
            | x::v'
              => (match v' in Vector.t _ n return S n = 2 -> _ with
                    | [] => fun H => !
                    | y::v''
                      => (match v'' in Vector.t _ n return S (S n) = 2 -> _ with
                            | [] => fun _ => (x, y)
                            | _::_ => fun H => !
                          end)
                  end)
          end eq_refl.

  Definition min_pair_by_dist : point.t * point.t -> point.t * point.t -> point.t * point.t
    := @min_by (point.t * point.t)
               point.distT
               point.dist_le
               point.dist_le_dec
               (fun ab => point.get_dist (fst ab) (snd ab)).

  Definition get_two_closest_of_three : t 3 -> point.t * point.t.
  Proof.
    intro v.
    inversion_clear v as [|x ? v']; rename v' into v.
    inversion_clear v as [|y ? v']; rename v' into v.
    inversion_clear v as [|z ? v']; rename v' into v.
    exact (min_pair_by_dist (min_pair_by_dist (x, y) (y, z))
                            (x, z)).
  Defined.

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

  Import point.Notations.
  Definition points_in_strip n (pts : t n) (median : point.t) (cur_closest_dist : point.distT)
  : list point.t
    := filter (fun pt => if (∥' median -- pt '∥ ≤ cur_closest_dist)%dec_dist
                         then true
                         else false)
              (Vector.to_list pts).
End NaivePointSet.
