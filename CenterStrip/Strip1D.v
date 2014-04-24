(** * The strip around the median in 1-D *)
Require Export CenterStrip.Core.

(** We can find the minimum or maximum of a list of points. *)
Module MidStrip1D (point : Point) <: Strip point.
  Import point.Notations.

  Definition get_left_most
  : forall ls : list point.t, ls <> [] -> point.t
    := let _ := point.x_le_dec in get_func.

  Definition get_right_most
  : forall ls : list point.t, ls <> [] -> point.t
    := (*let _ := point.x_le_preo in *)@get_func _ (flip point.x_le) (fun x y => point.x_le_dec y x) (*_*).

  (** Given two strips, we can find the right-most left point and
      left-most right point.  FIXME: Note: We don't handle duplicates correctly. *)
  Definition right_most_left_most (ls_left ls_right : list point.t)
             (H_left : ls_left <> []) (H_right : ls_right <> [])
  : point.t * point.t
    := (get_right_most H_left, get_left_most H_right).

  Local Ltac do_induct ls :=
    induction ls; simpl in *; intros; eauto;
    case_eq_if; intros; eauto;
    destruct_head or; repeat subst; eauto.

  (** We can also do it by filtering a single strip *)
  Program Definition right_most_left_most_from_median (ls : list point.t)
             (median : point.t)
             (H_left : exists pt, pt ∈ ls /\ pt ≤ median)
             (H_right : exists pt, pt ∈ ls /\ ~pt ≤ median)
  : point.t * point.t
    := @right_most_left_most
         (filter (fun pt => if (pt ≤ median)%dec then true else false) ls)
         (filter (fun pt => if (pt ≤ median)%dec then false else true) ls)
         _
         _.
  Next Obligation.
    match goal with
      | [ H : point.x_le ?x _ |- _ ] => generalize dependent x; clear
    end.
    do_induct ls.
  Qed.
  Next Obligation.
    match goal with
      | [ H : not (point.x_le ?x _) |- _ ] => generalize dependent x; clear
    end.
    do_induct ls.
  Qed.

  Definition get_closest_points_in_strip
          (median : point.t)
          (pre_closest_pair : point.t * point.t)
          (strip : list point.t)
  : point.t * point.t
    := let _ := point.x_le_preo in
       let _ := point.x_le_paro in
       let _ := point.x_le_dec in
       match (_ : Decidable (exists pt, pt ∈ strip /\ pt ≤ median)),
             (_ : Decidable (exists pt, pt ∈ strip /\ ~pt ≤ median)) with
         | left pf1, left pf2
           => let closest_in_strip := @right_most_left_most_from_median strip median pf1 pf2
              in if (∥' fst closest_in_strip -- snd closest_in_strip '∥
                      ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dec_dist
                 then closest_in_strip
                 else pre_closest_pair
         | _, _ => pre_closest_pair
       end.
  (*Lemma right_most_left_most_correct
        (ls_left ls_right : list point.t)
        (H_left : ls_left <> []) (H_right : ls_right <> [])
        (median : point.t)
        (left_correct : List.Forall (fun pt => pt ≤ median) ls_left)
        (right_correct : List.Forall (fun pt => median ≤ pt) ls_right)
        (no_dup_median : (median ∈ ls_left /\ ¬ median ∈ ls_right) \/ (¬ median ∈ ls_right))
        (triangle :*)
  Section correct.
    Context (median : point.t)
            (pre_closest_pair : point.t * point.t)
            (strip : list point.t).

    Let post_closest_pair := get_closest_points_in_strip median pre_closest_pair strip.

    Theorem get_closest_points_in_strip_closer
    : (∥' fst post_closest_pair -- snd post_closest_pair '∥
        ≤ ∥' fst pre_closest_pair -- snd pre_closest_pair '∥)%dist.
    Proof.
    Admitted.
  End correct.
End MidStrip1D.
