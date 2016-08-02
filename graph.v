From iris.algebra Require Import base cmra gmap.
From iris.prelude Require Import gmap mapset.

(* Definition of a doubly branching graphs and tree. *)
(* And theorems about those. *)

Section Graphs.
  Context {T : Type} {HD : ∀ x y : T, Decision (x = y)} {HC : @Countable T HD}.

  Definition Graph := gmap T (bool * (option T * option T)).

  Implicit Type g : Graph.

  Definition gmark g x :=
    match (g !! x) with
      | None => None
      | Some y => Some (fst y)
    end.

  Definition gleft g x :=
    match (g !! x) with
      | None => None
      | Some (_, (yl, _)) => yl
    end.

  Definition gright g x :=
    match (g !! x) with
      | None => None
      | Some (_, (_, yr)) => yr
    end.

  (* For some reason, perhaps a bug, type class inference can't find
gmap_lookup instance when defining an inductive! *)

  Inductive Path g (P : bool → bool) (x : T) : T → Type :=
  | Path_O : ∀ m l r, g !! x = Some (m, (l, r)) → P m → Path g P x x
  | Path_Sl : ∀ y z m r,
      Path g P x y → bool_decide (g !! y = Some (m, (Some z, r)))
      → P m → Path g P x z
  | Path_Sr : ∀ y z m l,
      Path g P x y → bool_decide (g !! y = Some (m, (l, Some z)))
      → P m → Path g P x z.

  (* The fragment of g satisfying P is a connected graph and x is in there. *)
  Definition connected (g : Graph) (P : bool → bool) (x : T) :=
    ∀ y m x1 x2, g !! y = Some (m, (x1, x2)) → P m → Path g P x y.

  (* The fragment of g satisfying P is a tree with root x. *)
  Record tree (g : Graph) P (x : T) :=
    {
      tree_connected : connected g P x;
      tree_connected_uniquely :
        ∀ y, y ∈ dom (gset _) g → ∀ (p p' : Path g P x y), p = p'
    }.

  (* The set of marked nodes of g *)
  Definition marked g := mapset_dom_with (λ x, bool_decide (fst x = true)) g.

  (* front of a set X of nodes in a graph g is the set of nodes that are
immediately reachable from nodes in X. *)
  Definition front g (X : gset T) : gset T :=
    Mapset
      (map_of_list
         (omap
            (λ x : T * (bool * (option T * option T)), if
                     bool_decide
                       (Exists
                          (λ t, bool_decide
                                  ((t.1 ∈ X) ∧
                                   (t.2.2.1 = Some (x.1)) ∨
                                   (t.2.2.2 = Some (x.1)))
                          ) (map_to_list g))
                   then Some (x.1, ()) else None
            ) (map_to_list g))).

  Record maximal_marked_tree g x :=
    {
      mmtr_tree : tree g (λ m, m) x;
      mmtr_maximal : front g (marked g) ⊆ (marked g)
    }.

  Definition combine_node_data
             (x y : option (bool * (option T * option T))) :
    option (bool * (option T * option T))
    :=
      match x, y with
      | Some (false, (xl, xr)), Some (false, (yl, yr)) =>
                         if bool_decide (xl = yl ∧ xr = yr) then
                           Some (false, (xl, xr))
                         else
                           None
      | Some (true, (xl, xr)), Some (false, (yl, yr)) => Some (true, (xl, xr))
      | Some (false, (xl, xr)), Some (true, (yl, yr)) => Some (true, (yl, yr))
      | _, _ => None
      end.

  Instance combine_node_data_DiagNone : DiagNone combine_node_data := eq_refl.

  Definition combine_graphs g1 g2 : option Graph :=
    if mapset_disjoint_dec (marked g1) (marked g2) then
      Some (merge combine_node_data g1 g2)
    else
      None.

  Lemma combine_graphs_comm g1 g2 : combine_graphs g1 g2 = combine_graphs g2 g1.
  Proof.
    unfold combine_graphs; repeat destruct mapset_disjoint_dec;
      trivial;
      try match goal with
            H : ¬ _ ⊥ _ |- _ => contradict H; apply disjoint_sym; trivial
          end.
    f_equal.
    apply merge_comm.
    - typeclasses eauto.
    - intros x.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn;
          trivial.
      repeat unfold bool_decide; repeat destruct option_eq_dec; cbn in *;
        repeat match goal with
                 H : ?A = _ |- _ => subst A
               end; trivial; try tauto.
  Qed.

  Lemma combine_graphs_dom_stable g1 g2 g3 :
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → combine_graphs g1 g2 = Some g3 → dom (gset _) g3 = dom (gset _) g1.
  Proof.
    intros H1 H2 H3.
    (apply mapset_eq => x);
      set (H1' := proj1 (mapset_eq _ _) H1 x); clearbody H1';
        destruct H1' as [H11 H12].
    specialize (H2 x).
    unfold combine_graphs in H3; destruct mapset_disjoint_dec as [d|nd];
      inversion H3; subst; clear H3.
    set (d' := proj1 (elem_of_disjoint _ _) d x); clearbody d'; clear d.
    revert H11 H12 d';
      rewrite /dom /gset_dom /mapset_dom ?elem_of_mapset_dom_with => H11 H12 d'.
    rewrite lookup_merge. split; intros [y [Hy _]].
    - destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn in *;
          trivial; try inversion Hy; eauto.
    - destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn in *;
      try (inversion Hy; fail); eauto.
      + exfalso; apply d'; eauto.
      + unfold bool_decide; repeat destruct option_eq_dec; subst; cbn; eauto;
        edestruct H2 as [H21 H22]; eauto; try tauto.
  Qed.

  Lemma combine_graphs_marked_eq_union g1 g2 g3 :
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → combine_graphs g1 g2 = Some g3 → marked g3 = (marked g1) ∪ (marked g2).
  Proof.
    intros H1 H2 H3.
    apply mapset_eq => x; split => Hx.
    - unfold combine_graphs in H3; destruct mapset_disjoint_dec as [d|nd];
      inversion H3; subst; clear H3.
      apply elem_of_mapset_dom_with in Hx. destruct Hx as [y [Hy1 Hy2]].
      rewrite lookup_merge in Hy1.
      apply elem_of_union.
      unfold marked; rewrite ?elem_of_mapset_dom_with.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|];
        (try (inversion Hy1; fail)); cbn in Hy1; cbn; eauto.
      unfold bool_decide in Hy1; repeat destruct option_eq_dec;
        subst; cbn in *; try discriminate; eauto.
    - set (H4 := combine_graphs_dom_stable _ _ _ H1 H2 H3);
        clearbody H4.
      unfold combine_graphs in H3; destruct mapset_disjoint_dec as [d|nd];
        inversion H3; subst; clear H3.
      apply elem_of_union in Hx.
      revert Hx; rewrite ?elem_of_mapset_dom_with => Hx.
      set (H5 := proj1 (mapset_eq _ _) H4 x). destruct H5 as [H51 H52].
      revert H51 H52. rewrite ?elem_of_dom. unfold is_Some.
      set (H6 := proj1 (mapset_eq _ _) (eq_trans H4 H1) x).
      destruct H6 as [H61 H62]. revert H61 H62. rewrite ?elem_of_dom.
      unfold is_Some.
      set (d' := proj1 (elem_of_disjoint _ _) d). specialize (d' x).
      revert d'; rewrite ?elem_of_mapset_dom_with.
      clear H1 H4 d. specialize (H2 x).
      rewrite ?lookup_merge. intros d H61 H62 H41 H42.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn in *;
          eauto;
          try match goal with
            H : _ → _ |- _ =>
            match type of H with
              ?A → ?B => cut (B → False);
                          [let H := fresh in intros H; exfalso; apply H; eauto|
                           clear; let H := fresh in intros H; firstorder]; fail
            end
          end.
      + exfalso. destruct Hx as [[y [Hy1 Hy2]]|[y [Hy1 Hy2]]]; inversion Hy1;
                   subst; cbn in *; trivial.
      + destruct Hx as [[y [Hy1 Hy2]]|[y [Hy1 Hy2]]]; discriminate.
  Qed.

  Lemma combine_graphs_marked_subseteq_union g1 g2 g3 :
    combine_graphs g1 g2 = Some g3 → marked g3 ⊆ (marked g1) ∪ (marked g2).
  Proof.
    intros H1.
    apply elem_of_subseteq => x Hx.
    unfold combine_graphs in H1; destruct mapset_disjoint_dec as [d|nd];
      inversion H1; subst; clear H1.
    apply elem_of_mapset_dom_with in Hx. destruct Hx as [y [Hy1 Hy2]].
    rewrite lookup_merge in Hy1.
    apply elem_of_union.
    unfold marked; rewrite ?elem_of_mapset_dom_with.
    destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
      destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|];
      (try (inversion Hy1; fail)); cbn in Hy1; cbn; eauto.
    unfold bool_decide in Hy1; repeat destruct option_eq_dec;
      subst; cbn in *; try discriminate; eauto.
  Qed.

  Lemma combine_maximal_marked_trees_both g1 g2 x x1 x2
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g1 x2)
        g3
        (Hc : combine_graphs g1 g2 = Some g3)
    : maximal_marked_tree (<[x := (true, (Some x1, Some x2))]> g3) x.
  Proof.
    repeat constructor.
    - intros w b ? ? H1 H2.
      rewrite insert_union_singleton_l in H1. 
      set (Hu := combine_graphs_marked_subseteq_union _ _ _ Hc); clearbody Hu.
      unfold combine_graphs in Hc; destruct mapset_disjoint_dec as [d|nd];
        inversion Hc; subst; clear Hc.
      admit.
    - intros w H1 p p'.
      admit.
    - admit.
  Admitted.

End Graphs.