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

  Inductive Path g (P : bool → bool) (x : T) : T → Type :=
  | Path_O : ∀ m l r, g !! x = Some (m, (l, r)) → P m → Path g P x x
  | Path_Sl : ∀ y z m r,
      bool_decide (g !! x = Some (m, (Some y, r)))
      → P m → Path g P y z → Path g P x z
  | Path_Sr : ∀ y z m l,
      bool_decide (g !! x = Some (m, (l, Some y)))
      → P m → Path g P y z → Path g P x z.

  Fixpoint trace_of {g P x y} (p : Path g P x y) {struct p} : list bool :=
    match p with
    | Path_O _ _ _ _ _ => nil
    | Path_Sl _ _ _ _ _ _ p' => cons true (trace_of p')
    | Path_Sr _ _ _ _ _ _ p' => cons false (trace_of p')
    end.

  Theorem trace_of_ext g P x y (p p' : Path g P x y) :
    trace_of p = trace_of p' → p = p'.
  Proof.
    intros H.
    induction p as
        [x m l r e Hm | x y z m r p Hm Hy IHp | x y z m r p Hm Hy IHp].
    - cbn in H.
      set (z := x) in p' at 2; set (Hz := eq_refl : x = z).
      transitivity
        (match Hz in _ = u return Path g P x u with
           eq_refl => Path_O g P x m l r e Hm
         end); [trivial|].
      clearbody Hz.
      change x with z at 2. change x with z in H at 2.
      clearbody z.
      destruct p' as [m' l' r' e' Hm'| |]; cbn in H; inversion H.
      set (e'' := eq_trans (eq_sym e') e). inversion e''; subst; clear e''.
      assert (Heq : e = e') by apply UIP; destruct Heq.
      replace Hz with (eq_refl x) by apply UIP.
      f_equal. by destruct (P m); destruct Hm; destruct Hm'.
    - destruct p' as [| y' z' m' r' p' Hm' Hy' |]; inversion H; subst.
      set (p'' := eq_trans
                    (eq_sym (proj1 (bool_decide_spec _) p'))
                    (proj1 (bool_decide_spec _) p));
        inversion p''; subst; clear p''.
      erewrite IHp; eauto.
      f_equal.
      + clear. unfold bool_decide in *.
          by destruct option_eq_dec; destruct p; destruct p'.
      + clear. by destruct (P m); destruct Hm; destruct Hm'.
    - destruct p' as [| | y' z' m' r' p' Hm' Hy']; inversion H; subst.
      set (p'' := eq_trans
                    (eq_sym (proj1 (bool_decide_spec _) p'))
                    (proj1 (bool_decide_spec _) p));
        inversion p''; subst; clear p''.
      erewrite IHp; eauto.
      f_equal.
      + clear. unfold bool_decide in *.
          by destruct option_eq_dec; destruct p; destruct p'.
      + clear. by destruct (P m); destruct Hm; destruct Hm'.
  Qed.

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
  Definition is_not_in_front g (x : T) w (_ : ()) :=
    match g !! w with
      | None => true
      | Some (_, (zl, zr)) =>
        if bool_decide (zl = Some x ∨ zr = Some x) then false else true
    end.

  Definition front g (X : gset T) : gset T :=
    Mapset (map_imap
              (λ u _, if
                 (map_Forall_dec (is_not_in_front g u) (mapset_car X)) then
                 None else Some () ) g).

  Lemma elem_of_front g X x :
    x ∈ front g X ↔
      x ∈ (dom (gset _) g) ∧
    ∃ y m l r, y ∈ X ∧ g !! y = Some (m, (l, r)) ∧ (l = Some x ∨ r = Some x).
  Proof.
    rewrite elem_of_dom /is_Some.
    split.
    - intros H. unfold elem_of, mapset_elem_of in H; cbn in H.
      rewrite lookup_imap in H. unfold mbind, option_bind in H.
      destruct (@lookup _ _ (gmap _ _) _ x g) as [[m [x1l x1r]]|];
        [|inversion H].
      destruct map_Forall_dec as [Hf|Hf]; [inversion H|].
      rewrite -> map_Forall_to_list in Hf.
      apply not_Forall_Exists in Hf; [|typeclasses eauto].
      apply Exists_exists in Hf. destruct Hf as [[y1 []] [Hf1 Hf2]]; cbn in *.
      unfold is_not_in_front in Hf2.
      split; eauto. exists y1.
      destruct (g !! y1) as [[m' [x1l' x1r']]|]; [|cbn in Hf2; tauto].
      exists m', x1l', x1r'; repeat split.
      + by apply elem_of_map_to_list in Hf1.
      + unfold bool_decide in Hf2; repeat destruct option_eq_dec;
          cbn in *; try tauto.
    - intros ((z & Hz) & y & m & l & r & H1 & H2 & H3).
      unfold front, elem_of, mapset_elem_of; cbn.
      rewrite lookup_imap; unfold mbind, option_bind.
      destruct (@lookup _ _ (gmap _ _) _ x g) as [[m' [x1l' x1r']]|];
        [|inversion Hz].
      destruct map_Forall_dec as [Hf|Hf]; trivial.
      contradict Hf. rewrite map_Forall_to_list.
      eapply Exists_not_Forall. apply Exists_exists.
      exists (y, ()); split; cbn.
      + by apply elem_of_map_to_list.
      + rewrite /is_not_in_front H2.
        unfold bool_decide; repeat destruct option_eq_dec; cbn; tauto.
  Qed.

  Lemma front_of_union g X1 X2 :
    front g (X1 ∪ X2) = front g X1 ∪ front g X2.
  Proof.
    apply mapset_eq => x. rewrite elem_of_union ?elem_of_front.
    split.
    - intros (Hd & y & m & l & r & H1 & H2 & H3).
      rewrite -> elem_of_union in H1; destruct H1 as [H1|H1]; eauto 10.
    - intros [(Hd & y & m & l & r & H1 & H2 & H3)|
              (Hd & y & m & l & r & H1 & H2 & H3)];
        repeat eexists; rewrite ?elem_of_union; eauto.
  Qed.

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

  Definition combine_graphs g1 g2 : Graph := (merge combine_node_data g1 g2).

  Lemma combine_graphs_comm g1 g2 : combine_graphs g1 g2 = combine_graphs g2 g1.
  Proof.
    unfold combine_graphs; repeat destruct mapset_disjoint_dec;
      trivial;
      try match goal with
            H : ¬ _ ⊥ _ |- _ => contradict H; apply disjoint_sym; trivial
          end.
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

  Lemma combine_graphs_dom_stable g1 g2 :
    (marked g1) ⊥ (marked g2) →
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → dom (gset _) (combine_graphs g1 g2) = dom (gset _) g1.
  Proof.
    intros d H1 H2.
    (apply mapset_eq => x);
      set (H1' := proj1 (mapset_eq _ _) H1 x); clearbody H1';
        destruct H1' as [H11 H12].
    specialize (H2 x).
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

  Lemma combine_graphs_marked_eq_union g1 g2 :
    (marked g1) ⊥ (marked g2) →
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → marked (combine_graphs g1 g2) = (marked g1) ∪ (marked g2).
  Proof.
    intros d H1 H2.
    apply mapset_eq => x; split => Hx.
    - apply elem_of_mapset_dom_with in Hx. destruct Hx as [y [Hy1 Hy2]].
      rewrite lookup_merge in Hy1.
      apply elem_of_union.
      unfold marked; rewrite ?elem_of_mapset_dom_with.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|];
        (try (inversion Hy1; fail)); cbn in Hy1; cbn; eauto.
      unfold bool_decide in Hy1; repeat destruct option_eq_dec;
        subst; cbn in *; try discriminate; eauto.
    - set (H4 := combine_graphs_dom_stable _ _ d H1 H2);
        clearbody H4.
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

  Definition convert_marked_Path_to_combine1 g1 g2 x y
    (d : (marked g1) ⊥ (marked g2))
    (Hdom : dom (gset T) g1 = dom (gset T) g2)
    (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
    (p : Path g1 (λ m, m) x y)
    : {q : Path (combine_graphs g1 g2) (λ m, m) x y | trace_of q = trace_of p}.
  Proof.
    set (d' := proj1 (elem_of_disjoint _ _) d); clearbody d';
      clear d; rename d' into d.
    set (Hdom' := proj1 (mapset_eq _ _) Hdom); clearbody Hdom';
      clear Hdom; rename Hdom' into Hdom.
    induction p as
        [x m l r e Hm | x y z m r Hy Hm p IHp | x y z m l Hy Hm p IHp].
    - destruct m; cbn in Hm; try tauto.
      eexists (Path_O _ _ _ true l r _ _); trivial.
      Unshelve. 2: trivial.
      rewrite /combine_graphs lookup_merge.
      specialize (Hagr x ); specialize (d x); specialize (Hdom x).
      revert d Hdom; rewrite /marked ?elem_of_mapset_dom_with => d [Hd1 Hd2].
      unfold Graph in *.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn in *;
          eauto; try (exfalso; apply d; eauto; fail);
            try match goal with
                  H : _ → _ |- _ =>
                  match type of H with
                    ?A → ?B =>
                    cut (B → False);
                      [let H := fresh in intros H; exfalso; apply H; eauto|
                       clear; let H := fresh in intros H; firstorder]; fail
                  end
                end.
      + inversion e.
    - destruct IHp as [q Hq].
      destruct m; cbn in Hm; try tauto.
      eexists (Path_Sl _ _ _ _ _ true r _ _ q); cbn; by rewrite Hq.
      Unshelve. 2: trivial.
      apply bool_decide_spec. apply bool_decide_spec in Hy.
      rewrite /combine_graphs lookup_merge.
      specialize (Hagr x ); specialize (d x); specialize (Hdom x).
      revert d Hdom; rewrite /marked ?elem_of_mapset_dom_with => d [Hd1 Hd2].
      unfold Graph in *.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn in *;
          eauto; try (exfalso; apply d; eauto; fail);
            try match goal with
                  H : _ → _ |- _ =>
                  match type of H with
                    ?A → ?B =>
                    cut (B → False);
                      [let H := fresh in intros H; exfalso; apply H; eauto|
                       clear; let H := fresh in intros H; firstorder]; fail
                  end
                end.
      + inversion Hy.
    - destruct IHp as [q Hq].
      destruct m; cbn in Hm; try tauto.
      eexists (Path_Sr _ _ _ _ _ true l _ _ q); cbn; by rewrite Hq.
      Unshelve. 2: trivial.
      apply bool_decide_spec. apply bool_decide_spec in Hy.
      rewrite /combine_graphs lookup_merge.
      specialize (Hagr x ); specialize (d x); specialize (Hdom x).
      revert d Hdom; rewrite /marked ?elem_of_mapset_dom_with => d [Hd1 Hd2].
      unfold Graph in *.
      destruct (@lookup _ _ (gmap _ _) _ x g1) as [[[] [x1l x1r]]|];
        destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|]; cbn in *;
          eauto; try (exfalso; apply d; eauto; fail);
            try match goal with
                  H : _ → _ |- _ =>
                  match type of H with
                    ?A → ?B =>
                    cut (B → False);
                      [let H := fresh in intros H; exfalso; apply H; eauto|
                       clear; let H := fresh in intros H; firstorder]; fail
                  end
                end.
      + inversion Hy.
  Qed.

  Definition convert_marked_Path_to_combine2 g1 g2 x y
    (d : (marked g1) ⊥ (marked g2))
    (Hdom : dom (gset T) g1 = dom (gset T) g2)
    (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
    (p : Path g2 (λ m, m) x y)
    : {q : Path (combine_graphs g1 g2) (λ m, m) x y | trace_of q = trace_of p}.
  Proof.
    rewrite combine_graphs_comm.
    eapply (convert_marked_Path_to_combine1 g2 g1); auto.
    intros z l1 l2 r1 r2 H1 H2. set (W := Hagr z l2 l1 r2 r1); intuition.
  Qed.

  (* initially proven, perhaps useless *)
  Lemma combine_graphs_marked_subseteq_union g1 g2 :
    (marked g1) ⊥ (marked g2)
    → marked (combine_graphs g1 g2) ⊆ (marked g1) ∪ (marked g2).
  Proof.
    intros d H1.
    apply elem_of_subseteq => x Hx.
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
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g1 x2)
        g3
    : maximal_marked_tree (<[x := (true, (Some x1, Some x2))]>
                           (combine_graphs g1 g2)) x.
  Proof.
    repeat constructor.
    - intros w b ? ? H1 H2.
      rewrite insert_union_singleton_l in H1.
      set (Hu := combine_graphs_marked_eq_union _ _ d Hdom Hagr); clearbody Hu.
      admit.
    - intros w H1 p p'.
      admit.
    - admit.
  Admitted.

End Graphs.