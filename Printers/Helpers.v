Require Export Ascii String List Arith Omega Vector List.
Require Export Algorithm.Full1D.
Require Export Printers.Nat.
Import NatPrinter.

Local Open Scope string_scope.

Module Export PrinterHelpers.
  Lemma ne_S_0 {x} : S x <> 0. Proof. omega. Qed.
  Lemma ne_SS_1 {x} : S (S x) <> 1. Proof. omega. Qed.

  Definition focus {T} (_ : T) := True.
  Definition focusI {T} {x : T} : focus x := I.
  Global Opaque focus.

  Definition make_star_points st
    := ("*",
        ((Vector.to_list (projT2 (ClosestPoints1D.state.left_points st)))
           ++ (Vector.to_list (projT2 (ClosestPoints1D.state.right_points st))))%list).
  Definition make_oh_points {A} (pts : A * A)
    := ("o", (fst pts)::(snd pts)::List.nil).

  Class auto (T : Type) := auto_intro : T.

  Global Hint Extern 1 (auto _) => hnf; apply ne_S_0 : typeclass_instances.
  Global Hint Extern 1 (auto _) => hnf; apply ne_SS_1 : typeclass_instances.

  Definition make_tree_from_list points
             `{H' : auto (Datatypes.length points <> 0)}
             `{H'' : auto (Datatypes.length points <> 1)}
    := match @ClosestPoints1D.make_algorithm_tree_from_point_set
               _ (Vector.of_list points) with
         | inl x => x
         | inr (left H) => match H' H with end
         | inr (right H) => match H'' H with end
       end.

  Definition make_display_from_tree s points :=
    ("                            "::(snd
                                        (@ClosestPoints1D.walk_algorithm_tree_in_order
                                           _ _

                                           (** at the leaves, what do we do? *)
                                           (** we display the other points as [.], the current points as [*], and the closest points as [o] *)
                                           (fun pts lines =>
                                              let disp_points' := make_oh_points pts::(".", points)::List.nil in
                                              (lines,
                                               string_list_of_nats_with_lines_and_points
                                                 points
                                                 lines
                                                 disp_points'))



                                           (** before each split, what do we display? *)
                                           (** We display the new median line as [|], the old one as [:] *)
                                           (fun st lines => let lines' := ((ClosestPoints1D.state.median st)::lines)%list in
                                                            let star := make_star_points st in
                                                            (lines',
                                                             (string_list_of_nats_with_lines_and_points
                                                                points
                                                                lines'
                                                                (star::(".", points)::List.nil))::List.nil))

                                           (** after we come back from the left side, what do we display? *)
                                           (** We display the points we care about, keeping the [o] points, but removing the [.] points *)
                                           (fun st lines =>
                                              let disp_points := ((make_oh_points (ClosestPoints1D.state.closest_left_points st))
                                                                    ::make_star_points st
                                                                    ::(".", points)
                                                                    ::List.nil) in
                                              (lines,
                                               string_list_of_nats_with_lines_and_points
                                                 points
                                                 lines
                                                 disp_points::List.nil))


                                           (** after we come back from the right side, what do we display? *)
                                           (** First we display the points we care about, keeping the [o] points.
                          Then we display the center strip.
                          Then we display the center strip with the closest points on it.
                          Then we display the closest points we know about so far. *)
                                           (fun st lines =>
                                              (lines,
                                               (((** First, we display the points we care about, with the [o] points on the right *)
                                                   string_list_of_nats_with_lines_and_points
                                                     points
                                                     lines
                                                     ((make_oh_points (ClosestPoints1D.state.closest_right_points st))
                                                        ::make_star_points st
                                                        ::(".", points)
                                                        ::List.nil))
                                                  ::((** Then, we display the center strip *)
                                                    string_list_of_nats_with_lines_and_points
                                                      points
                                                      lines
                                                      (("*", ClosestPoints1D.state.center_points st)
                                                         ::(".", points)
                                                         ::List.nil))
                                                  ::((** Then, we display the center strip with its closest points *)
                                                    string_list_of_nats_with_lines_and_points
                                                      points
                                                      lines
                                                      ((make_oh_points (ClosestPoints1D.state.closest_center_points st))
                                                         ::("*", ClosestPoints1D.state.center_points st)
                                                         ::(".", points)
                                                         ::List.nil))
                                                  ::((** Then, we display the closest points we know about so far *)
                                                    string_list_of_nats_with_lines_and_points
                                                      points
                                                      lines
                                                      ((make_oh_points (ClosestPoints1D.state.closest_points st))
                                                         ::make_star_points st
                                                         ::(".", points)
                                                         ::List.nil))
                                                  ::List.nil)))
                                           s
                                           List.nil))).

  Ltac step_then p n_hyp tac :=
    let l := match type of p with
               | focus ?l => constr:(l)
             end in
    let n := match type of n_hyp with
               | focus ?n => constr:(n)
             end in
    let s := constr:(@nth_default _ "DONE" l n) in
    let s' := (eval lazy in s) in
    idtac s';
      tac n_hyp n.

  Ltac next p n_hyp :=
    step_then p n_hyp ltac:(fun n_hyp n => replace_hyp n_hyp (focusI : focus (S n))).
  Ltac prev p n_hyp :=
    step_then p n_hyp ltac:(fun n_hyp n => replace_hyp n_hyp (focusI : focus (pred n))).

  Definition make_display_from_list points `{H' : _, H'' : _} :=
    make_display_from_tree (@make_tree_from_list points H' H'') points.
End PrinterHelpers.
