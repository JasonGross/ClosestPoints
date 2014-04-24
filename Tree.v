(** * A tree with data *)
Require Export Recdef.
Require Export CommonDefinitions.

Section tree.
  Variable node_data : Type.
  Variable leaf_data : Type.

  Inductive tree :=
  | Leaf : leaf_data -> tree
  | Node : tree -> node_data -> option tree -> tree.

  Fixpoint map_nodes_with_data
           (data : tree -> option tree -> node_data)
           (l : list tree)
  : list tree
    := match l with
         | nil => nil
         | x::nil => (Node x
                           (data x None)
                           None)::nil
         | x::y::rest => (Node x
                               (data x (Some y))
                               (Some y))
                           ::map_nodes_with_data data rest
       end.

  Fixpoint list_rect' {A} l (P : list A -> Type)
        (H0 : P nil)
        (H1 : forall x, P nil -> P (x::nil))
        (H2 : forall x y rest, P rest -> P (x::y::rest))
  : P l
    := match l as l return P l with
         | nil => H0
         | x::nil => H1 _ H0
         | x::y::rest => H2 x y rest (@list_rect' _ rest P H0 H1 H2)
       end.

  Lemma map_nodes_with_data_length data x y rest
  : List.length (map_nodes_with_data data (x::y::rest)) < List.length (x::y::rest).
  Proof.
    eapply (@list_rect' _ rest); simpl.
    - repeat constructor.
    - intros; repeat constructor.
    - intros. apply lt_S_n in H.
      repeat apply lt_n_S.
      etransitivity; try eassumption.
      auto.
  Defined.

  Function list_to_tree_helper data (l : list tree) {measure List.length l}
  : option tree
    := match map_nodes_with_data data l with
         | nil => None
         | x::nil => Some x
         | l' => list_to_tree_helper data l'
       end.
  Proof.
    intros.
    subst.
    destruct l as [|?[|?[|?[ ]]]];
    try solve [ inversion_clear teq; auto ].
    rewrite <- teq.
    apply map_nodes_with_data_length.
  Defined.

  Definition list_to_tree data (l : list leaf_data)
  : option tree
    := list_to_tree_helper data (map Leaf l).
End tree.
