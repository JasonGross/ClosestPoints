(** * Brute Force Algorithm *)
Require Import CommonDefinitions.
(** We implement a simpler version of the recursive
    closest-points-in-a-plane algorithm from 6.850 Lecture 1.  In
    particular, we consider the 1-D version of the algorithm (which
    doesn't actually buy us any speed over sorting the list). *)

(** First, we implement a brute force check algorithm. *)


(*(** We spec out what the algorithm does, functionally; it returns the
    smallest distance between distinct points.  If the list has not
    enough distinct points, we do not require anything at all. *)
Definition points_are_distinct_and_in_list (pts : list nat) (min_pts : nat * nat) : Prop
  := fst min_pts <> snd min_pts /\ List.In (fst min_pts) pts /\ List.In (snd min_pts) pts.*)

(*Fixpoint list_has_enough_distinct_points (pts : list nat) : Prop
  := match pts with
       | nil => False
       | _::nil => False
       | x::(y::zs) as pts'
         => if (x = y)%dec
            then list_has_enough_distinct_points pts'
            else True
     end.

Definition is_min_dist_points_helper (pts : list nat) (pt1 pt2 : nat) : Prop
  := List.Forall (fun pt => List.Forall (fun pt' => if (pt = pt')%dec
                                                    then True
                                                    else ∥' pt1 -- pt2 '∥ ≤ ∥' pt -- pt' '∥)
                                        pts)
                 pts.

Definition is_min_dist_points (pts : list nat) (min_pts : option (nat * nat)) : Prop
  := NoDup pts
     -> match pts, min_pts with
          | nil, _ => True
          | _::nil, _ => True
          | pts, None => False
          | pts, Some (pt1, pt2) => is_min_dist_points_helper pts pt1 pt2
        end.*)

(** We implement the brute force algorithm as a sanity check. *)
Fixpoint min_dist_pts_brute_force (pts : list nat) : option (nat * nat)
  := match pts with
       | nil => None
       | pt::pts' => fold_right (option_f
                                   (fun pts1 pts2 => if (∥' fst pts1 -- snd pts1 '∥ ≤ ∥' fst pts2 -- snd pts2 '∥)%dec
                                                     then pts1
                                                     else pts2))
                                (min_dist_pts_brute_force pts')
                                (map (fun pt' => if (pt = pt')%dec then None else Some (pt, pt'))
                                     pts')
     end.

Definition min_dist_brute_force (pts : list nat) : option nat :=
  match min_dist_pts_brute_force pts with
    | None => None
    | Some (p, q) => Some ∥' p -- q '∥
  end.

(** Sanity check *)
Eval compute in min_dist_pts_brute_force [1; 4; 5; 9].
(**
<<
     = Some (4, 5)
     : option (nat * nat)
>> *)
Eval compute in min_dist_brute_force [1; 4; 5; 9].
(**
<<
     = Some 1
     : option nat
>> *)


(*Lemma min_dist_pts_brute_force_correct (pts : list nat)
: is_min_dist_points pts (min_dist_pts_brute_force pts).
Proof.
  induction pts as [|? pts];
  [ | induction pts ];
  try solve [ simpl in *; repeat intro; intuition eauto ].
  simpl.
  intro.
  intro.
  intros.
  Focus 2.
  intro.
  destruct pts.
  intuition eauto.
  simpl.
  simpl in *.
  case_eq (min_dist_pts_brute_force pts).
  Focus 2.
  intro H.

  simpl.
  erewrite IHpts by eassumption.
  intros.

  destruct pts; simpl in *; eauto.
  case_eq_if; simpl in *.

  simpl in *.
  simpl in *.
  intros.
  simpl in *.
  intuition eauto.
  intuition eauto.
  simpl in *.
  intro.
  simpl in *.
  intro H.
  simpl in *.
  hnf.
  induction pts; try reflexivity.
  destruct pts; try reflexivity.
  destruct pts; try reflexivity.
  simpl in *.
  case_eq_if; eauto.
  simpl; intros.
  split.
  hnf; simpl.
  intuition eauto.
*)
