Require Export Sorted.
Require Export CommonDefinitions Point.NatPointCore2D Printers.Nat2D.
(** Is the point in the strip about a given median?  We use an informative type so that we don't care about the implementation. *)
Definition point_in_strip (median_below median_above : nat)
           (median_correct : {median_below = median_above} + {S median_below = median_above})
           (dist : nat)
           (pt : point)
           (x := pt.(x))
           (y := pt.(y))
: {if (x < median_above)%dec then median_above - x <= dist else x - median_below <= dist}
  + {if (x < median_above)%dec then median_above - x > dist else x - median_below > dist}.
Proof.
  destruct (x < median_above)%dec;
  destruct median_correct; subst;
  apply le_gt_dec.
Defined.


(** Given a list of points, a new point, and a distance, add the new point to the list, and remove any points whose y-coordinate is further from the given point than the distance. *)
Definition update_holding_points (holding_points : list point) (new_point : point) (distance : nat) : list point
  := new_point::(filter (fun pt => if (max (pt.(y) - new_point.(y)) (new_point.(y) - pt.(y)) <= distance)%dec
                                   then true
                                   else false)
                        holding_points).

Check (eq_refl : (update_holding_points ((1,2)::(3,4)::(5,6)::nil) (7,8) 6)
                 = (7, 8) :: (1, 2) :: (3, 4) :: (5, 6) :: nil).

(** f takes in the accumulator, the current point, and a list of holding points *)
(** Note: the list of holding points should probably be backed with a doubly-linked list.  But there will be at most a constant number of points in it, so we don't actually care. *)
Definition cmp_y : relation point := (fun pt1 pt2 => pt1.(y) <= pt2.(y)).
Fixpoint fold_points_in_strip {T} (acc : T) (f : point -> list point -> T -> T)
        (strip : list point)
        (strip_sorted : Sorted cmp_y strip)
        (median_below median_above : nat)
        (median_correct : {median_below = median_above} + {S median_below = median_above})
        (dist : nat)
        (holding_points : list point)
: T.
Proof.
  refine (match strip as strip return Sorted cmp_y strip -> T with
            | nil => fun _ => acc
            | pt::pts =>
              fun is_sorted =>
                let pts_is_sorted := match is_sorted return Sorted cmp_y pts with
                                       | _ => _
                                     end in
                if point_in_strip median_correct dist pt
                then let new_acc := f pt holding_points acc in
                     let new_holding_points := update_holding_points holding_points pt dist in
                     @fold_points_in_strip _ new_acc f pts pts_is_sorted _ _ median_correct dist new_holding_points
                else fold_points_in_strip _ acc f pts pts_is_sorted _ _ median_correct dist holding_points
          end strip_sorted).
  revert is_sorted; clear; intro; abstract (inversion_clear is_sorted; assumption).
Defined.

(** Now we find the minimum distance between points in a strip *)
Definition find_min_square_dist_in_strip
           (median_below median_above : nat)
           (median_correct : {median_below = median_above} + {S median_below = median_above})
           (strip : list point) (strip_sorted : Sorted cmp_y strip)
           (half_width : nat)
: option nat
  := fold_points_in_strip
       None
       (fun pt pts cur_min => option_min
                                (fold_left option_min
                                           (map (fun pt' => Some ∥ pt' -- pt ∥²) pts)
                                           None)
                                cur_min)
       strip_sorted
       median_correct
       half_width
       nil.

Goal True.
  pose (fun H => @find_min_square_dist_in_strip 2 3 (right eq_refl) ((1,2)::(3,4)::(5,6)::(7,8)::(9,10)::(11,12)::nil) H 2).
  cbv beta delta [find_min_square_dist_in_strip] in o.
  cbv beta delta [fold_points_in_strip] in o.



Goal True.
  print_list ((1,1)::(2,3)::(4,5)::nil).
  print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (3::nil).
  print_list_with_lines ((1,1)::(2,3)::(4,5)::nil) (1::3::nil).

  print_grid (.
  match eval hnf in grid with
    | nil => idtac "a"
    | ?r::?rs => idtac r; idtac "a"; print_grid rs
  end.
