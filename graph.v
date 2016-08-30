From iris.algebra Require Import base cmra gmap.
From iris.prelude Require Import gmap mapset.
Require Import Coq.Logic.Eqdep_dec.

(* The version with Decision so we can use typeclasses eauto *)
Lemma UIP_dec' : ∀ A : Type,
    (∀ x y : A, Decision (x = y)) → ∀ (x y : A) (p1 p2 : x = y), p1 = p2.
Proof. intros; by apply UIP_dec. Qed.

(* Definition of a doubly branching graphs and tree. *)
(* And theorems about those. *)

Section Graphs.
  Context {T : Type} {HD : ∀ x y : T, Decision (x = y)} {HC : @Countable T HD}.

  Definition graph := gmap T (bool * (option T * option T)).

  Implicit Type g : graph.

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

  Inductive Path g (P : bool → bool) (x y : T) : Type :=
  | Path_O : ∀ m l r, g !! x = Some (m, (l, r)) → P m → x = y → Path g P x y
  | Path_Sl : ∀ z m r,
      bool_decide (g !! x = Some (m, (Some z, r)))
      → P m → Path g P z y → Path g P x y
  | Path_Sr : ∀ z m l,
      bool_decide (g !! x = Some (m, (l, Some z)))
      → P m → Path g P z y → Path g P x y.

  Lemma Path_dom g P x y : Path g P x y → x ∈ dom (gset T) g.
  Proof.
    intros p.
    rewrite elem_of_dom; unfold is_Some.
    induction p as
        [x m l r e Hm | x y z m r p Hm Hy IHp | x y z m r p Hm Hy IHp];
      try apply bool_decide_spec in p; eauto.
  Qed.

  Lemma Path_P g P x y : Path g P x y → {u | g !! x = Some u ∧ P (fst u)}.
  Proof.
    intros p.
    induction p as
        [x m l r e Hm | x y z m r p Hm Hy IHp | x y z m r p Hm Hy IHp];
      try apply bool_decide_spec in p; eauto.
  Qed.

  Lemma Path_P' g P x y : Path g P x y → {u | g !! y = Some u ∧ P (fst u)}.
  Proof.
    intros p.
    induction p as
        [x m l r e Hm | x y z m r p Hm Hy IHp | x y z m r p Hm Hy IHp];
      try apply bool_decide_spec in p; subst; eauto.
  Qed.

  Fixpoint trace_of {g P x y} (p : Path g P x y) {struct p} : list bool :=
    match p with
    | Path_O _ _ _ _ _ _ => nil
    | Path_Sl _ _ _ _ _ p' => cons true (trace_of p')
    | Path_Sr _ _ _ _ _ p' => cons false (trace_of p')
    end.

    Theorem trace_of_ext g P x y (p p' : Path g P x y) :
    trace_of p = trace_of p' → p = p'.
  Proof.
    intros H.
    induction p as
        [x y m l r e Hm Heq | x y z m r p Hm Hy IHp | x y z m r p Hm Hy IHp].
    - cbn in H.
      destruct p' as [m' l' r' e' Hm' Heq'| |]; cbn in H; inversion H; subst.
      set (e'' := eq_trans (eq_sym e') e). inversion e''; subst; clear e''.
      assert (Heq : e = e'). apply UIP_dec'; typeclasses eauto. destruct Heq.
      f_equal. by destruct (P m); destruct Hm; destruct Hm'.
      apply UIP_dec'; typeclasses eauto.
    - destruct p' as [| z' m' r' p' Hm' Hy' |]; inversion H; subst.
      set (p'' := eq_trans
                    (eq_sym (proj1 (bool_decide_spec _) p'))
                    (proj1 (bool_decide_spec _) p));
        inversion p''; subst; clear p''.
      erewrite IHp; eauto.
      f_equal.
      + clear. unfold bool_decide in *.
          by destruct option_eq_dec; destruct p; destruct p'.
      + clear. by destruct (P m); destruct Hm; destruct Hm'.
    - destruct p' as [| | z' m' r' p' Hm' Hy']; inversion H; subst.
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
  Definition connected g (P : bool → bool) (x : T) :=
    ∀ y m x1 x2, g !! y = Some (m, (x1, x2)) → P m → Path g P x y.

  (* The fragment of g satisfying P is a tree with root x. *)
  Record tree g P (x : T) :=
    {
      tree_connected : connected g P x;
      tree_connected_uniquely :
        ∀ y (p p' : Path g P x y), p = p'
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

  Definition combine_graphs g1 g2 : graph := (merge combine_node_data g1 g2).

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

  Hint Resolve combine_graphs_dom_stable.

  Lemma combine_graphs_dom_stable' g1 g2 :
    (marked g1) ⊥ (marked g2) →
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → dom (gset _) (combine_graphs g1 g2) = dom (gset _) g2.
  Proof.
    intros H1 H2 H3. rewrite combine_graphs_comm.
    eapply combine_graphs_dom_stable; auto.
    intros x l1 l2 r1 r2 ? ?. destruct (H3 x l2 l1 r2 r1); eauto.
  Qed.

  Hint Resolve combine_graphs_dom_stable'.

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
                  ?A → ?B =>
                  cut (B → False);
                    [let H := fresh in intros H; exfalso; apply H; eauto|
                     clear; let H := fresh in intros []; congruence]; fail
                end
              end.
      + exfalso. destruct Hx as [[y [Hy1 Hy2]]|[y [Hy1 Hy2]]]; inversion Hy1;
                   subst; cbn in *; trivial.
      + destruct Hx as [[y [Hy1 Hy2]]|[y [Hy1 Hy2]]]; discriminate.
  Qed.

  Lemma marked_combine_graphs_marked g1 g2 z :
    (marked g1) ⊥ (marked g2) →
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → z ∈ marked g1 → z ∈ marked (combine_graphs g1 g2).
  Proof.
    intros. rewrite combine_graphs_marked_eq_union; eauto.
    apply elem_of_union; auto.
  Qed.

  Hint Resolve marked_combine_graphs_marked.

  Lemma marked_combine_graphs_marked' g1 g2 z :
    (marked g1) ⊥ (marked g2) →
    dom (gset _) g1 = dom (gset _) g2 →
    (∀ x l1 l2 r1 r2,
        @lookup _ _ (gmap _ _) _ x g1 = Some (false, (l1, r1)) →
        @lookup _ _ (gmap _ _) _ x g2 = Some (false, (l2, r2)) →
        l1 = l2 ∧ r1 = r2
    ) → z ∈ marked g2 → z ∈ marked (combine_graphs g1 g2).
  Proof.
    intros. rewrite combine_graphs_marked_eq_union; eauto.
    apply elem_of_union; auto.
  Qed.

  Hint Resolve marked_combine_graphs_marked'.

  Lemma combine_graphs_marked_agree g1 g2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom: dom (gset _) g1 = dom (gset _) g2)
        u l r
    : g1 !! u = Some (true, (l, r)) →
      (combine_graphs g1 g2) !! u = Some (true, (l, r)).
  Proof.
    intros H.
    rewrite /combine_graphs lookup_merge.
    set (d' := proj1 (elem_of_disjoint _ _) d); specialize (d' u); clear d;
      revert d'; rewrite ?elem_of_mapset_dom_with => d.
    set (Hdom' := proj1 (mapset_eq _ _) Hdom); specialize (Hdom' u); clear Hdom;
      revert Hdom'; rewrite ?elem_of_mapset_dom_with; intros [Hdm1 Hdm2].
    rewrite H in d, Hdm1 Hdm2; rewrite H.
    destruct (@lookup _ _ (gmap _ _) _ u g2) as [[[] [x2l x2r]]|];
      cbn in *; eauto.
    + exfalso; apply d; eauto.
    + match type of Hdm1 with
        ?A → ?B => cut (B → False);
                    [let H := fresh in intros H; exfalso; apply H; eauto|
                     clear; let H := fresh in intros H; firstorder]
      end.
  Qed.

  Hint Resolve combine_graphs_marked_agree.

  Lemma combine_graphs_marked_agree' g1 g2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom: dom (gset _) g1 = dom (gset _) g2)
        u l r
    : g2 !! u = Some (true, (l, r)) →
      (combine_graphs g1 g2) !! u = Some (true, (l, r)).
  Proof.
    intros H. rewrite combine_graphs_comm.
    apply combine_graphs_marked_agree; auto.
  Qed.

  Hint Resolve combine_graphs_marked_agree'.

  Lemma combine_graphs_not_marked_agree g1 g2 x v
        (Hg1x : (g1 !! x = Some (false, v)))
        (Hg2x : (g2 !! x = Some (false, v)))
    : (combine_graphs g1 g2) !! x = Some (false, v).
  Proof.
    rewrite /combine_graphs lookup_merge Hg1x Hg2x; cbn.
    destruct v as [[] []];
      unfold bool_decide; repeat (destruct decide; cbn);
      repeat destruct option_eq_dec; cbn; firstorder.
  Qed.

  Hint Resolve combine_graphs_not_marked_agree.

  Lemma combine_graphs_marked_back g1 g2 x x1 x2 :
    x ∈ marked g1 →
    combine_graphs g1 g2 !! x = Some (true, (x1, x2)) →
    g1 !! x = Some (true, (x1, x2)).
  Proof.
    intros H1 H2. apply elem_of_mapset_dom_with in H1.
    destruct H1 as [[m [l r]] [H11 H12]].
    apply bool_decide_spec in H12; cbn in H12; subst.
    revert H2; unfold combine_graphs; rewrite lookup_merge => H2.
    rewrite H11 in H2.
    destruct (@lookup _ _ (gmap _ _) _ x g2) as [[[] [x2l x2r]]|];
      cbn in *; try inversion H2; subst; trivial.
  Qed.

  Lemma marking_agrees g x v1 v2 u l r :
    match (g !! x) with
    | Some (b, _) => b = false
    | _ => False
    end → g !! u = Some (true, (l, r)) →
    <[x := (true, (v1, v2))]> g !! u = Some (true, (l, r)).
  Proof.
    intros H1 H2.
    destruct (decide (x = u)); subst.
    - rewrite H2 in H1; inversion H1.
    - by rewrite lookup_insert_ne.
  Qed.

  Definition convert_marked_Path g g' x y
             (Himpl : ∀ u l r,
                 g !! u = Some (true, (l, r)) → g' !! u = Some (true, (l, r)))
             (p : Path g (λ m, m) x y)
    : {q : Path g' (λ m, m) x y | trace_of q = trace_of p}.
  Proof.
    induction p as
        [x y m l r e Hm Heq | x y z m r Hy Hm p IHp | x y z m l Hy Hm p IHp];
      destruct m; cbn in Hm; try tauto.
    - eexists (Path_O _ _ _ _ true l r _ _ _); trivial.
      Unshelve. all: cbn; auto.
    - destruct IHp as [q Hq].
      eexists (Path_Sl _ _ _ _ _ true r _ _ q); cbn; by rewrite Hq.
      Unshelve. 2: trivial.
      apply bool_decide_spec. apply bool_decide_spec in Hy.
      apply Himpl; cbn; auto.
    - destruct IHp as [q Hq].
      eexists (Path_Sr _ _ _ _ _ true l _ _ q); cbn; by rewrite Hq.
      Unshelve. 2: trivial.
      apply bool_decide_spec. apply bool_decide_spec in Hy.
      apply Himpl; cbn; auto.
  Qed.

  Definition convert_back_marked_Path g g' x y
             (Hdom : dom (gset T) g = dom (gset T) g')
             (Himpl : ∀ u l r,
                 g !! u = Some (true, (l, r)) → g' !! u = Some (true, (l, r)))
             (Hmm : front g (marked g) ⊆ (marked g))
             (xm : x ∈ marked g)
             (p : Path g' (λ m, m) x y)
    : {q : Path g (λ m, m) x y | trace_of q = trace_of p}.
  Proof.
    assert (xm' : match (g !! x) with
                 | Some (b, _) => b = true
                 | _ => False
                  end).
    { apply elem_of_mapset_dom_with in xm.
      unfold graph in *.
      destruct (@lookup _ _ (gmap _ _) _ x g) as [[[] [x1l x1r]]|]; trivial.
      + destruct xm as [[? [? ?]] [H1 H2]]; inversion H1; subst; inversion H2.
      + destruct xm as [[? [? ?]] [H1 H2]]; inversion H1. }
    clear xm; rename xm' into xm.
    set (Hdm1 x := proj1 (proj1 (mapset_eq _ _) Hdom x)); clearbody Hdm1.
    set (Hdm2 x := proj2 (proj1 (mapset_eq _ _) Hdom x)); clearbody Hdm2.
    clear Hdom.
    revert Hdm1 Hdm2; rewrite ?elem_of_mapset_dom_with; intros Hdm1 Hdm2.
    set (Hmm' := proj1 (elem_of_subseteq _ _) Hmm); clearbody Hmm'; clear Hmm.
    rename Hmm' into Hmm.
    induction p as
        [x y m l r e Hm Heq | x y z m r Hy Hm p IHp | x y z m l Hy Hm p IHp];
      destruct m; cbn in Hm; try tauto.
    - eexists (Path_O _ _ _ _ true l r _ _ _); trivial.
      Unshelve. all: cbn; auto.
      specialize (Himpl x). unfold graph in *.
      destruct (@lookup _ _ (gmap _ _) _ x g) as [[[] [x1l x1r]]|];
        inversion xm.
      specialize (Himpl x1l x1r eq_refl). by rewrite -Himpl -e.
    - cbn in *. apply bool_decide_spec in Hy.
      unfold graph in *.
      specialize (Himpl x).
      destruct (@lookup _ _ (gmap _ _) _ x g) as [[[] [x1l x1r]]|] eqn:Heq;
        inversion xm.
      specialize (Himpl x1l x1r eq_refl).
      set (Hh := eq_trans (eq_sym Himpl) Hy); inversion Hh; subst; clear Hh.
      assert (Hmy : z ∈ marked g).
      { apply Hmm; rewrite elem_of_front. split.
        - apply Hdm2; eapply Path_dom; eauto.
        - eexists x, true, (Some z), r; repeat split; eauto.
          rewrite /marked elem_of_mapset_dom_with; eauto. }
      unfold marked in Hmy. apply elem_of_mapset_dom_with in Hmy.
      destruct (@lookup _ _ (gmap _ _) _ z g) as [[[] [x1l x1r]]|] eqn: Heq'.
      + destruct IHp as [q Hq]; trivial.
        eexists (Path_Sl _ _ _ _ _ true r _ _ q); cbn; by rewrite Hq.
        Unshelve. 2: trivial.
        apply bool_decide_spec; trivial.
      + exfalso; destruct Hmy as [v [Hmy1 Hmy2]];
          inversion Hmy1; subst; cbn in *; trivial.
      + exfalso; destruct Hmy as [v [Hmy1 Hmy2]]; inversion Hmy1.
    - cbn in *. apply bool_decide_spec in Hy.
      unfold graph in *.
      specialize (Himpl x).
      destruct (@lookup _ _ (gmap _ _) _ x g) as [[[] [x1l x1r]]|] eqn:Heq;
        inversion xm.
      specialize (Himpl x1l x1r eq_refl).
      set (Hh := eq_trans (eq_sym Himpl) Hy); inversion Hh; subst; clear Hh.
      assert (Hmy : z ∈ marked g).
      { apply Hmm; rewrite elem_of_front. split.
        - apply Hdm2; eapply Path_dom; eauto.
        - eexists x, true, l, (Some z); repeat split; eauto.
          rewrite /marked elem_of_mapset_dom_with; eauto. }
      unfold marked in Hmy. apply elem_of_mapset_dom_with in Hmy.
      destruct (@lookup _ _ (gmap _ _) _ z g) as [[[] [x1l x1r]]|] eqn: Heq'.
      + destruct IHp as [q Hq]; trivial.
        eexists (Path_Sr _ _ _ _ _ true l _ _ q); cbn; by rewrite Hq.
        Unshelve. 2: trivial.
        apply bool_decide_spec; trivial.
      + exfalso; destruct Hmy as [v [Hmy1 Hmy2]];
          inversion Hmy1; subst; cbn in *; trivial.
      + exfalso; destruct Hmy as [v [Hmy1 Hmy2]]; inversion Hmy1.
  Qed.

  Definition convert_marked_Path_to_combine1 g1 g2 x y
             (d : (marked g1) ⊥ (marked g2))
             (Hdom : dom (gset T) g1 = dom (gset T) g2)
             (p : Path g1 (λ m, m) x y)
  : {q : Path (combine_graphs g1 g2) (λ m, m) x y | trace_of q = trace_of p}.
  Proof.
    apply convert_marked_Path.
    apply combine_graphs_marked_agree; auto.
  Qed.

  Definition convert_marked_Path_to_combine2 g1 g2 x y
             (d : (marked g1) ⊥ (marked g2))
             (Hdom : dom (gset T) g1 = dom (gset T) g2)
             (p : Path g2 (λ m, m) x y)
    : {q : Path (combine_graphs g1 g2) (λ m, m) x y | trace_of q = trace_of p}.
  Proof.
    rewrite combine_graphs_comm.
    eapply (convert_marked_Path_to_combine1 g2 g1); auto.
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

  Lemma marked_in_dom g x : x ∈ marked g → x ∈ dom (gset _) g.
  Proof.
    intros H1; apply elem_of_mapset_dom_with in H1.
    destruct H1 as [u [H1 H2]].
    apply elem_of_dom; unfold is_Some; eauto.
  Qed.

  Hint Resolve marked_in_dom.

  Lemma combine_mmtr_connected g1 g2 x x1 x2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g2 x2)
    : connected (<[x := (true, (Some x1, Some x2))]> (combine_graphs g1 g2))
                (λ m, m) x.
  Proof.
    destruct t1 as [[cn1 t1] mm1]; destruct t2 as [[cn2 t2] mm2].
    intros w b ? ? H1 H2.
    destruct b; inversion H2; clear H2.
    destruct (decide (x = w)); subst.
    + econstructor; eauto.
    + rewrite lookup_insert_ne in H1; trivial.
      assert (Hw : w ∈ marked (combine_graphs g1 g2)).
      { apply elem_of_mapset_dom_with; rewrite H1; eauto. }
      rewrite (combine_graphs_marked_eq_union _ _ d Hdom Hagr) in Hw.
      apply elem_of_union in Hw.
      destruct (decide (w ∈ marked g1)) as [w1|w1];
        destruct (decide (w ∈ marked g2)) as [w2|w2].
      * exfalso; eapply (proj1 (elem_of_disjoint _ _) d); eauto.
      * econstructor 2; try rewrite lookup_insert; eauto.
        refine ((λ H p, proj1_sig (convert_marked_Path
                                     (combine_graphs g1 g2) _ _ _ H p))
                  _ _).
        -- intros. eapply marking_agrees; eauto.
           erewrite combine_graphs_not_marked_agree; eauto.
        -- apply convert_marked_Path_to_combine1; trivial.
           eapply cn1. eapply combine_graphs_marked_back. all: eauto.
      * econstructor 3; try rewrite lookup_insert; eauto.
        refine ((λ H p, proj1_sig (convert_marked_Path
                                     (combine_graphs g1 g2) _ _ _ H p))
                  _ _).
        -- intros. eapply marking_agrees; eauto.
           erewrite combine_graphs_not_marked_agree; eauto.
        -- apply convert_marked_Path_to_combine2; trivial.
           eapply cn2. eapply combine_graphs_marked_back. all: eauto.
           rewrite combine_graphs_comm; eauto.
      * exfalso; tauto.
  Qed.

  Lemma Path_marked g x y : Path g (λ m, m) x y → x ∈ marked g.
  Proof.
    intros p. apply elem_of_mapset_dom_with.
    destruct (Path_P _ _ _ _ p) as [[[] ?] [? ?]]; eauto.
  Qed.

  Lemma Path_marked' g x y : Path g (λ m, m) x y → y ∈ marked g.
  Proof.
    intros p. apply elem_of_mapset_dom_with.
    destruct (Path_P' _ _ _ _ p) as [[[] ?] [? ?]]; eauto.
  Qed.

  Lemma marked_in g x v y :
    y ≠ x → y ∈ marked (<[x:=(true, v)]> g) → y ∈ marked g.
  Proof.
    intros H.
    rewrite /marked ?elem_of_mapset_dom_with lookup_insert_ne; auto.
  Qed.

  Lemma maximally_marked_combine g1 g2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hmm1 : front g1 (marked g1) ⊆ (marked g1))
        (Hmm2 : front g2 (marked g2) ⊆ (marked g2))
    : front (combine_graphs g1 g2) (marked (combine_graphs g1 g2))
            ⊆ (marked (combine_graphs g1 g2)).
  Proof.
    apply elem_of_subseteq => x H1.
    apply elem_of_front in H1. destruct H1 as (H1&(y&m&l&r&H21&H22&H23)).
    set (H21' := H21); clearbody H21'.
    revert H21; rewrite ?combine_graphs_marked_eq_union; trivial => H21.
    apply elem_of_union; apply elem_of_union in H21.
    apply elem_of_mapset_dom_with in H21'.
    destruct H21' as [[m' [l' r']] [H31 H32]].
    set (He := eq_trans (eq_sym H31) H22); inversion He; subst; clear He.
    destruct m; inversion H32; clear H31 H32.
    set (Hmm1' := proj1 (elem_of_subseteq _ _) Hmm1); clearbody Hmm1';
      clear Hmm1; rename Hmm1' into Hmm1.
    set (Hmm2' := proj1 (elem_of_subseteq _ _) Hmm2); clearbody Hmm2';
      clear Hmm2; rename Hmm2' into Hmm2.
    destruct H21 as [H21|H21].
    - left; apply Hmm1.
      apply elem_of_front; split.
      + by rewrite combine_graphs_dom_stable in H1.
      + apply combine_graphs_marked_back in H22;  eauto 10.
    - right; apply Hmm2.
      apply elem_of_front; split.
      + rewrite combine_graphs_comm in H1.
        rewrite combine_graphs_dom_stable in H1; eauto.
        intros z l1 l2 r1 r2 ? ?. destruct (Hagr z l2 l1 r2 r1); auto.
      + rewrite combine_graphs_comm in H22.
        apply combine_graphs_marked_back in H22;  eauto 10.
  Qed.

  Hint Resolve maximally_marked_combine.

  Local Hint Extern 1 =>
  match goal with
    |- ∀ (u : T) (l r : option T),
      combine_graphs ?g1 ?g2 !! u = Some (true, (l, r))
      → <[?x:=(true, (Some ?z, Some ?x2))]>
        (combine_graphs ?g1 ?g2) !! u = Some (true, (l, r)) =>
    intros; apply marking_agrees;
      try erewrite (combine_graphs_not_marked_agree _ _ x); eauto
  end.

  Local Hint Extern 1 =>
  match goal with
    |- ∀ (u0 : T) (l r : option T),
   ?g1 !! u0 = Some (true, (l, r))
   → <[?x:=(true, (Some ?x1, Some ?x2))]> (combine_graphs ?g1 ?g2) !! u0 =
     Some (true, (l, r)) =>
    intros; apply marking_agrees;
      try erewrite (combine_graphs_not_marked_agree _ _ x); eauto
  end.

  Local Hint Extern 1 =>
  match goal with
    |- ∀ (u0 : T) (l r : option T),
   ?g2 !! u0 = Some (true, (l, r))
   → <[?x:=(true, (Some ?x1, Some ?x2))]> (combine_graphs ?g1 ?g2) !! u0 =
     Some (true, (l, r)) =>
    intros; apply marking_agrees;
      try erewrite (combine_graphs_not_marked_agree _ _ x); eauto
  end.

  Lemma dom_helper_gen g x v v'
        (Hg1x : g !! x = Some (false, v))
    :
      dom (gset T) g = dom (gset T) (<[x:=(true, v')]> g).
  Proof.
    apply mapset_eq => z. rewrite ?elem_of_dom; unfold is_Some.
    destruct (decide (z = x)); subst.
    - rewrite lookup_insert. intuition eauto.
    - rewrite lookup_insert_ne; auto.
  Qed.

  Hint Resolve dom_helper_gen.

  Lemma dom_helper'1 g1 g2 x v
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : g1 !! x = Some (false, v))
        (Hg2x : g2 !! x = Some (false, v))
    :
      dom (gset T) g1 =
      dom (gset T) (<[x:=(true, v)]> (combine_graphs g1 g2)).
  Proof.
    erewrite <- dom_helper_gen; eauto; by rewrite combine_graphs_dom_stable.
  Qed.

  Hint Resolve dom_helper'1.

  Lemma dom_helper'2 g1 g2 x v
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : g1 !! x = Some (false, v))
        (Hg2x : g2 !! x = Some (false, v))
    :
      dom (gset T) g2 =
      dom (gset T) (<[x:=(true, v)]> (combine_graphs g1 g2)).
  Proof.
    erewrite <- dom_helper_gen; eauto; by rewrite combine_graphs_dom_stable'.
  Qed.

  Hint Resolve dom_helper'2.

  Lemma marked_helper g z x
        (H : x ∈ marked g)
        (cn : connected g (λ m : bool, m) z)
        : z ∈ marked g.
  Proof.
    unfold connected in cn.
    apply elem_of_mapset_dom_with in H.
    destruct H as [[[] [l r]] [H1 H2]]; inversion H2.
    eapply Path_marked; eauto.
  Qed.

  Hint Resolve marked_helper.

  Lemma not_marked_helper g1 g2 x v
    (Hg1x : g1 !! x = Some (false, v))
    (Hg2x : g2 !! x = Some (false, v))
    :
      x ∉ marked (combine_graphs g1 g2).
  Proof.
    intros H1.
    apply elem_of_mapset_dom_with in H1.
    erewrite combine_graphs_not_marked_agree in H1; eauto.
    destruct H1 as [z [H1 H2]]; inversion H1; subst; tauto.
  Qed.

  Hint Resolve not_marked_helper.

  Lemma combine_mmtr_noPath1 g1 g2 x x1 x2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g2 x2)
        u (um : u ∈ marked g1)
    : Path (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2))
           (λ m, m) x1 x → False.
  Proof.
    intros p.
    set (t1' := t1); set (t2' := t2); clearbody t1' t2';
      destruct t1 as [[cn1 t1] mm1]; destruct t2 as [[cn2 t2] mm2].
    edestruct (λ H1 H2 H3 H4,
               convert_back_marked_Path
                 (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 p)
      as [q _]; eauto.
    apply Path_marked' in q. eapply (not_marked_helper g1 g2); eauto.
  Qed.

  Lemma combine_mmtr_noPath2 g1 g2 x x1 x2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g2 x2)
        u (um : u ∈ marked g2)
    : Path (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2))
           (λ m, m) x2 x → False.
  Proof.
    intros p.
    set (t1' := t1); set (t2' := t2); clearbody t1' t2';
      destruct t1 as [[cn1 t1] mm1]; destruct t2 as [[cn2 t2] mm2].
    edestruct (λ H1 H2 H3 H4,
               convert_back_marked_Path
                 (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 p)
      as [q _]; eauto.
    apply Path_marked' in q. eapply (not_marked_helper g1 g2); eauto.
  Qed.

  Lemma combine_mmtr_noPath3 g1 g2 x x1 x2 y
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g2 x2)
        (ym : y ∈ marked g2)
        u (um : u ∈ marked g1)
    : Path (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2))
           (λ m, m) x1 y → False.
  Proof.
    intros p.
    set (t1' := t1); set (t2' := t2); clearbody t1' t2';
      destruct t1 as [[cn1 t1] mm1]; destruct t2 as [[cn2 t2] mm2].
    edestruct (λ H1 H2 H3 H4,
               convert_back_marked_Path
                 (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 p)
      as [q _]; eauto.
    edestruct (λ H1 H2 H3 H4,
               convert_back_marked_Path
                 g1 _ _ _ H1 H2 H3 H4 p)
      as [q' _]; eauto.
    apply Path_marked' in q'.
    eapply (proj1 (elem_of_disjoint _ _) d); eauto.
  Qed.

  Lemma combine_mmtr_noPath4 g1 g2 x x1 x2 y
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g2 x2)
        (ym : y ∈ marked g1)
        u (um : u ∈ marked g2)
    : Path (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2))
           (λ m, m) x2 y → False.
  Proof.
    intros p.
    set (t1' := t1); set (t2' := t2); clearbody t1' t2';
      destruct t1 as [[cn1 t1] mm1]; destruct t2 as [[cn2 t2] mm2].
    edestruct (λ H1 H2 H3 H4,
               convert_back_marked_Path
                 (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 p)
      as [q _]; eauto.
    edestruct (λ H1 H2 H3 H4,
               convert_back_marked_Path
                 g2 _ _ _ H1 H2 H3 H4 p)
      as [q' _]; eauto.
    apply Path_marked' in q'.
    eapply (proj1 (elem_of_disjoint _ _) d); eauto.
  Qed.

  Lemma combine_mmtr_connected_uniquely g1 g2 x x1 x2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (t1 : maximal_marked_tree g1 x1)
        (t2 : maximal_marked_tree g2 x2)
        (g1x1m : x1 ∈ marked g1)
        (g2x2m : x2 ∈ marked g2)
    : ∀ (y : T)
        (p p' : Path (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2))
                     (λ m : bool, m) x y), p = p'.
  Proof.
    set (t1' := t1); set (t2' := t2); clearbody t1' t2';
      destruct t1 as [[cn1 t1] mm1]; destruct t2 as [[cn2 t2] mm2].
    intros w p p'.
    destruct (decide (x = w)); subst.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + destruct p' as
            [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
        * by apply trace_of_ext.
        *  exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
           inversion p'; subst.
           eapply combine_mmtr_noPath1; eauto.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
          inversion p'; subst.
          eapply combine_mmtr_noPath2; eauto.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p; subst.
        eapply combine_mmtr_noPath1; eauto.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p; subst.
        eapply combine_mmtr_noPath2; eauto.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + tauto.
      + set (Hp' := Path_marked' _ _ _ p'); apply marked_in in Hp'; auto.
        rewrite combine_graphs_marked_eq_union in Hp'; trivial.
        apply elem_of_union in Hp'.
        destruct (decide (w ∈ marked g1)) as [w1|w1];
        destruct (decide (w ∈ marked g2)) as [w2|w2].
        * exfalso; eapply (proj1 (elem_of_disjoint _ _) d); eauto.
        * destruct p' as
              [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
          -- tauto.
          -- set (He := eq_trans (eq_sym (proj1 (bool_decide_spec _) p'))
                                 (proj1 (bool_decide_spec _) p));
               inversion He; subst; clear He.
             apply trace_of_ext; cbn; f_equal.
             apply bool_decide_spec in p; rewrite lookup_insert in p;
             inversion p; subst.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 Hy)
               as [q Hq]; eauto.
             rewrite -Hq.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 Hy')
               as [q' Hq']; eauto.
             rewrite -Hq'.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          g1 _ _ _ H1 H2 H3 H4 q)
               as [v Hv]; [symmetry| | | |]; eauto.
             rewrite -Hv.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          g1 _ _ _ H1 H2 H3 H4 q')
               as [v' Hv']; [symmetry| | | |]; eauto.
             rewrite -Hv'.
             auto with f_equal.
          -- exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
             inversion p'; subst.
             eapply combine_mmtr_noPath4; eauto.
        * exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
          inversion p; subst.
          eapply combine_mmtr_noPath3; eauto.
        * tauto.
      + set (Hp' := Path_marked' _ _ _ p'); apply marked_in in Hp'; auto.
        rewrite combine_graphs_marked_eq_union in Hp'; trivial.
        apply elem_of_union in Hp'.
        destruct (decide (w ∈ marked g1)) as [w1|w1];
        destruct (decide (w ∈ marked g2)) as [w2|w2].
        * exfalso; eapply (proj1 (elem_of_disjoint _ _) d); eauto.
        * exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
          inversion p; subst.
          eapply combine_mmtr_noPath4; eauto.
        * destruct p' as
              [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
          -- tauto.
          -- exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
             inversion p'; subst.
             eapply combine_mmtr_noPath3; eauto.
          -- set (He := eq_trans (eq_sym (proj1 (bool_decide_spec _) p'))
                                 (proj1 (bool_decide_spec _) p));
               inversion He; subst; clear He.
             apply trace_of_ext; cbn; f_equal.
             apply bool_decide_spec in p; rewrite lookup_insert in p;
             inversion p; subst.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 Hy)
               as [q Hq]; eauto.
             rewrite -Hq.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          (combine_graphs g1 g2) _ _ _ H1 H2 H3 H4 Hy')
               as [q' Hq']; eauto.
             rewrite -Hq'.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          g2 _ _ _ H1 H2 H3 H4 q)
               as [v Hv]; [symmetry | | | |]; eauto.
             rewrite -Hv.
             edestruct (λ H1 H2 H3 H4,
                        convert_back_marked_Path
                          g2 _ _ _ H1 H2 H3 H4 q')
               as [v' Hv']; [symmetry| | | |]; eauto.
             rewrite -Hv'.
             auto with f_equal.
        * tauto.
  Qed.

  Lemma marked_insert g x u: marked (<[x:=(true, u)]> g) = {[x]} ∪ marked g.
  Proof.
    apply mapset_eq => z. rewrite elem_of_union.
    unfold marked; rewrite ?elem_of_mapset_dom_with.
    rewrite elem_of_singleton.
    destruct (decide (z = x)); subst;
      [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    - split; eauto.
    - split; eauto. intros [H1|H1]; try tauto.
  Qed.

  Lemma front_insert g (x : T) (x1 x2 : option T)
        (Hx1 :
           match x1 with
           | Some y1 => y1 ∈ dom (gset _) g
           | None => True
           end)
        (Hx2 :
           match x2 with
           | Some y2 => y2 ∈ dom (gset _) g
           | None => True
           end)
        (Hgx : match g !! x with
               | Some (m, _) => m = false
               | None => False
               end)
    :
      front (<[x:=(true, (x1, x2))]> g) (marked (<[x:=(true, (x1, x2))]> g)) =
      match x1 with | Some y1 => {[ y1 ]} | None => ∅ end
        ∪
        match x2 with | Some y2 => {[ y2 ]} | None => ∅ end
        ∪ (front g (marked g)).
  Proof.
    apply mapset_eq => z.
    rewrite ?elem_of_union ?elem_of_front.
    unfold marked; rewrite ?elem_of_mapset_dom_with.
    split.
    - intros (H1 & (y & m & l & r & H31 & H32 & H33)).
      rewrite -> elem_of_mapset_dom_with in H31.
       destruct (decide (y = x)); subst.
      + destruct (decide (z = x)); subst.
        * rewrite lookup_insert in H1, H31, H32.
          inversion H32; subst.
          destruct H33; subst; left; [left|right]; by apply elem_of_singleton.
        * rewrite lookup_insert in H31, H32.
          rewrite lookup_insert_ne in H1; eauto.
          inversion H32; subst.
          destruct H33; subst; left; [left|right]; by apply elem_of_singleton.
      + rewrite lookup_insert_ne in H31, H32; eauto.
        rewrite H32 in H31. destruct H31 as (u & H41 & H42).
        inversion H41; subst.
        destruct (decide (z = x)); subst.
        * unfold graph in *.
          destruct (@lookup _ _ (gmap _ _) _ x g) as [[m' [xl xr]]|];
            [|inversion Hgx].
          right; split; eauto.
          repeat eexists; try rewrite elem_of_mapset_dom_with; eauto.
        * destruct H1 as [? [H1 _]].
          rewrite lookup_insert_ne in H1; auto.
          right; split; eauto.
          repeat eexists; try rewrite elem_of_mapset_dom_with; eauto.
    - intros [[H1|H1]|H1].
      + destruct x1 as [y1|]; try (inversion H1; fail).
        revert H1; rewrite elem_of_singleton => H1; subst.
        apply elem_of_dom in Hx1; unfold is_Some in Hx1.
        unfold graph in *.
        destruct (@lookup _ _ (gmap _ _) _ x g) as [[m' [xl xr]]|];
          [|inversion Hgx].
        destruct (decide (y1 = x)); subst.
        * rewrite lookup_insert; split; eauto.
          exists x; do 3 eexists. rewrite elem_of_mapset_dom_with.
          rewrite lookup_insert; split; eauto.
        * rewrite lookup_insert_ne; auto.
          split.
          -- destruct Hx1; eauto.
          -- exists x; do 3 eexists. rewrite lookup_insert.
             split; eauto.
             rewrite elem_of_mapset_dom_with lookup_insert.
             eexists (true, _); eauto.
      + destruct x2 as [y2|]; try (inversion H1; fail).
        revert H1; rewrite elem_of_singleton => H1; subst.
        apply elem_of_dom in Hx2; unfold is_Some in Hx2.
        unfold graph in *.
        destruct (@lookup _ _ (gmap _ _) _ x g) as [[m' [xl xr]]|];
          [|inversion Hgx].
        destruct (decide (y2 = x)); subst.
        * rewrite lookup_insert; split; eauto.
          exists x; do 3 eexists. rewrite elem_of_mapset_dom_with.
          rewrite lookup_insert; split; eauto.
        * rewrite lookup_insert_ne; auto.
          split.
          -- destruct Hx2; eauto.
          -- exists x; do 3 eexists. rewrite lookup_insert.
             split; eauto.
             rewrite elem_of_mapset_dom_with lookup_insert.
             eexists (true, _); eauto.
      + destruct H1 as (H1 & y & m & l & r & H2 & H3 & H4).
          revert H2; rewrite elem_of_mapset_dom_with => H2.
        destruct (decide (y = x)); subst.
        * unfold graph in *.
          destruct (@lookup _ _ (gmap _ _) _ x g) as [[m' [xl xr]]|];
            [|inversion Hgx].
          rewrite Hgx in H3. inversion H3; subst.
          destruct H2 as [? [H21 H22]]; inversion H21; subst; inversion H22.
        * split.
          -- destruct (decide (z = x)); subst;
               [rewrite lookup_insert| rewrite lookup_insert_ne]; eauto.
          -- eexists y; do 3 eexists.
             rewrite elem_of_mapset_dom_with.
             rewrite lookup_insert_ne; eauto.
  Qed.

  Lemma combine_mmtr_maximally_marked g1 g2 x x1 x2
        (d : (marked g1) ⊥ (marked g2))
        (Hdom : dom (gset T) g1 = dom (gset T) g2)
        (Hagr : ∀ (x : T) (l1 l2 r1 r2 : option T),
            g1 !! x = Some (false, (l1, r1)) → g2 !! x = Some (false, (l2, r2))
            → l1 = l2 ∧ r1 = r2)
        (Hg1x : (g1 !! x = Some (false, (Some x1, Some x2))))
        (Hg2x : (g2 !! x = Some (false, (Some x1, Some x2))))
        (g1x1m : x1 ∈ marked g1)
        (g2x2m : x2 ∈ marked g2)
        (Hmg1 : front g1 (marked g1) ⊆ marked g1)
        (Hmg2 : front g2 (marked g2) ⊆ marked g2)
    :
    front (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2))
          (marked (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2)))
          ⊆ marked (<[x:=(true, (Some x1, Some x2))]> (combine_graphs g1 g2)).
  Proof.
    rewrite front_insert; eauto.
    - apply elem_of_subseteq => z.
      rewrite marked_insert ?elem_of_union; auto.
      rewrite ?elem_of_singleton.
      intros [[-> | ->]|H1]; eauto.
      right.
      apply maximally_marked_combine; eauto.
    - erewrite combine_graphs_not_marked_agree; eauto.
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
        (t2 : maximal_marked_tree g2 x2)
        (g1x1m : x1 ∈ marked g1)
        (g2x2m : x2 ∈ marked g2)
    : maximal_marked_tree (<[x := (true, (Some x1, Some x2))]>
                           (combine_graphs g1 g2)) x.
  Proof.
    repeat constructor.
    - by apply combine_mmtr_connected.
    - by apply combine_mmtr_connected_uniquely.
    - destruct t1; destruct t2;
        apply combine_mmtr_maximally_marked; auto.
  Qed.

  Lemma left_mmtr_connected g x x1 u
        (Hg2x : (g !! x = Some (false, (Some x1, u))))
        (t1 : maximal_marked_tree g x1)
    : connected (<[x := (true, (Some x1, None))]> g) (λ m, m) x.
  Proof.
    destruct t1 as [[cn1 t1] mm1].
    intros w b ? ? H1 H2.
    destruct b; inversion H2; clear H2.
    destruct (decide (x = w)); subst.
    - econstructor; eauto.
    - rewrite lookup_insert_ne in H1; trivial.
      + econstructor 2; try rewrite lookup_insert; eauto.
        refine ((λ H p, proj1_sig (convert_marked_Path g _ _ _ H p))
                  _ _).
        * intros v l r H2.
          destruct (decide (x = v)); subst;
            [rewrite lookup_insert| rewrite lookup_insert_ne]; eauto.
          rewrite H2 in Hg2x; inversion Hg2x.
        * eapply cn1; eauto.
  Qed.

  Local Hint Extern 1 =>
  match goal with
    H : ?g !! ?x = _ |- ∀ (u : T) (l r : option T),
      ?g !! u = Some (true, (l, r))
      → <[?x:=(true, (?x1, ?x2))]> ?g !! u = Some (true, (l, r)) =>
    intros; apply marking_agrees; try rewrite H; auto
  end.

  Lemma left_mmtr_noPath g x x1 u
        (Hgx : (g !! x = Some (false, (Some x1, u))))
        (t1 : maximal_marked_tree g x1)
        v (um : v ∈ marked g)
    : Path (<[x:=(true, (Some x1, None))]> g) (λ m, m) x1 x → False.
  Proof.
    intros p.
    destruct t1 as [[cn1 t1] mm1].
    edestruct (λ H1 H2 H3 H4, convert_back_marked_Path g _ _ _ H1 H2 H3 H4 p)
      as [q _]; eauto.
    apply Path_marked', elem_of_mapset_dom_with in q; rewrite Hgx in q.
    destruct q as [? [H1 H2]]; inversion H1; subst; inversion H2.
  Qed.

  Lemma left_mmtr_connected_uniquely g x x1 u
        (Hgx : (g !! x = Some (false, (Some x1, u))))
        (t1 : maximal_marked_tree g x1)
        (g1x1m : x1 ∈ marked g)
  : ∀ (y : T) (p p' : Path (<[x:=(true, (Some x1, None))]> g)
                           (λ m : bool, m) x y), p = p'.
  Proof.
    set (t1' := t1); clearbody t1'; destruct t1 as [[cn1 t1] mm1].
    intros w p p'. destruct (decide (x = w)); subst.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + destruct p' as
            [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
        * by apply trace_of_ext.
        *  exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
           inversion p'; subst.
           eapply left_mmtr_noPath; eauto.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
          inversion p'; subst.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p; subst.
        eapply left_mmtr_noPath; eauto.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p; subst.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + tauto.
      + set (Hp' := Path_marked' _ _ _ p'). apply marked_in in Hp'; auto.
        destruct p' as
            [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
        * tauto.
        * set (He := eq_trans (eq_sym (proj1 (bool_decide_spec _) p'))
                              (proj1 (bool_decide_spec _) p));
            inversion He; subst; clear He.
          apply trace_of_ext; cbn; f_equal.
          apply bool_decide_spec in p; rewrite lookup_insert in p;
            inversion p; subst.
          edestruct (λ H1 H2 H3 H4,
                     convert_back_marked_Path g _ _ _ H1 H2 H3 H4 Hy)
            as [q Hq]; eauto.
          rewrite -Hq.
          edestruct (λ H1 H2 H3 H4,
                     convert_back_marked_Path g _ _ _ H1 H2 H3 H4 Hy')
            as [q' Hq']; eauto.
          rewrite -Hq'.
          auto with f_equal.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
          inversion p'; subst.
      + set (Hp' := Path_marked' _ _ _ p'); apply marked_in in Hp'; auto.
        * exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
          inversion p; subst.
  Qed.

  Lemma left_mmtr_maximally_marked g x x1 u
        (Hgx : (g !! x = Some (false, (Some x1, u))))
        (t1 : maximal_marked_tree g x1)
        (gx1m : x1 ∈ marked g)
    :
      front (<[x:=(true, (Some x1, None))]> g)
            (marked (<[x:=(true, (Some x1, None))]> g))
          ⊆ marked (<[x:=(true, (Some x1, None))]> g).
  Proof.
    destruct t1 as [[cn1 t1] mm1]. rewrite front_insert; eauto.
    - apply elem_of_subseteq => z.
      rewrite marked_insert ?elem_of_union; auto.
      rewrite ?elem_of_singleton.
      intros [[-> | H1]|H1]; eauto.
      inversion H1.
    - rewrite Hgx; trivial.
  Qed.

  Lemma left_maximal_marked_trees g x x1 u
        (Hg1x : (g !! x = Some (false, (Some x1, u))))
        (t1 : maximal_marked_tree g x1)
        (g1x1m : x1 ∈ marked g)
    : maximal_marked_tree (<[x := (true, (Some x1, None))]> g) x.
  Proof.
    repeat constructor.
    - by eapply left_mmtr_connected.
    - by eapply left_mmtr_connected_uniquely.
    - eapply left_mmtr_maximally_marked; eauto.
  Qed.

  Lemma right_mmtr_connected g x x2 u
        (Hg2x : (g !! x = Some (false, (u, Some x2))))
        (t1 : maximal_marked_tree g x2)
    : connected (<[x := (true, (None, Some x2))]> g) (λ m, m) x.
  Proof.
    destruct t1 as [[cn1 t1] mm1].
    intros w b ? ? H1 H2.
    destruct b; inversion H2; clear H2.
    destruct (decide (x = w)); subst.
    - econstructor; eauto.
    - rewrite lookup_insert_ne in H1; trivial.
      + econstructor 3; try rewrite lookup_insert; eauto.
        refine ((λ H p, proj1_sig (convert_marked_Path g _ _ _ H p))
                  _ _).
        * intros v l r H2.
          destruct (decide (x = v)); subst;
            [rewrite lookup_insert| rewrite lookup_insert_ne]; eauto.
          rewrite H2 in Hg2x; inversion Hg2x.
        * eapply cn1; eauto.
  Qed.

  Lemma right_mmtr_noPath g x x2 u
        (Hgx : (g !! x = Some (false, (u, Some x2))))
        (t1 : maximal_marked_tree g x2)
        v (um : v ∈ marked g)
    : Path (<[x:=(true, (None, Some x2))]> g) (λ m, m) x2 x → False.
  Proof.
    intros p.
    destruct t1 as [[cn1 t1] mm1].
    edestruct (λ H1 H2 H3 H4, convert_back_marked_Path g _ _ _ H1 H2 H3 H4 p)
      as [q _]; eauto.
    apply Path_marked', elem_of_mapset_dom_with in q; rewrite Hgx in q.
    destruct q as [? [H1 H2]]; inversion H1; subst; inversion H2.
  Qed.

  Lemma right_mmtr_connected_uniquely g x x2 u
        (Hgx : (g !! x = Some (false, (u, Some x2))))
        (t1 : maximal_marked_tree g x2)
        (g1x1m : x2 ∈ marked g)
  : ∀ (y : T) (p p' : Path (<[x:=(true, (None, Some x2))]> g)
                           (λ m : bool, m) x y), p = p'.
  Proof.
    set (t1' := t1); clearbody t1'; destruct t1 as [[cn1 t1] mm1].
    intros w p p'. destruct (decide (x = w)); subst.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + destruct p' as
            [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
        * by apply trace_of_ext.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
          inversion p'; subst.
        *  exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
           inversion p'; subst.
           eapply right_mmtr_noPath; eauto.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p; subst.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p; subst.
        eapply right_mmtr_noPath; eauto.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + tauto.
      + set (Hp' := Path_marked' _ _ _ p'); apply marked_in in Hp'; auto.
        * exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
          inversion p; subst.
      + set (Hp' := Path_marked' _ _ _ p'). apply marked_in in Hp'; auto.
        destruct p' as
            [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
        * tauto.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
          inversion p'; subst.
        * set (He := eq_trans (eq_sym (proj1 (bool_decide_spec _) p'))
                              (proj1 (bool_decide_spec _) p));
            inversion He; subst; clear He.
          apply trace_of_ext; cbn; f_equal.
          apply bool_decide_spec in p; rewrite lookup_insert in p;
            inversion p; subst.
          edestruct (λ H1 H2 H3 H4,
                     convert_back_marked_Path g _ _ _ H1 H2 H3 H4 Hy)
            as [q Hq]; eauto.
          rewrite -Hq.
          edestruct (λ H1 H2 H3 H4,
                     convert_back_marked_Path g _ _ _ H1 H2 H3 H4 Hy')
            as [q' Hq']; eauto.
          rewrite -Hq'.
          auto with f_equal.
  Qed.

  Lemma right_mmtr_maximally_marked g x x2 u
        (Hgx : (g !! x = Some (false, (u, Some x2))))
        (t1 : maximal_marked_tree g x2)
        (gx2m : x2 ∈ marked g)
    :
      front (<[x:=(true, (None, Some x2))]> g)
            (marked (<[x:=(true, (None, Some x2))]> g))
          ⊆ marked (<[x:=(true, (None, Some x2))]> g).
  Proof.
    destruct t1 as [[cn1 t1] mm1]. rewrite front_insert; eauto.
    - apply elem_of_subseteq => z.
      rewrite marked_insert ?elem_of_union; auto.
      rewrite ?elem_of_singleton.
      intros [[H1 | ->]|H1]; eauto.
      inversion H1.
    - rewrite Hgx; trivial.
  Qed.

  Lemma right_maximal_marked_trees g x x2 u
        (Hg1x : (g !! x = Some (false, (u, Some x2))))
        (t1 : maximal_marked_tree g x2)
        (g1x1m : x2 ∈ marked g)
    : maximal_marked_tree (<[x := (true, (None, Some x2))]> g) x.
  Proof.
    repeat constructor.
    - by eapply right_mmtr_connected.
    - by eapply right_mmtr_connected_uniquely.
    - by eapply right_mmtr_maximally_marked.
  Qed.

  Lemma is_marked g w u :
    g !! w = Some (true, u) → w ∈ marked g.
  Proof. intros H1. apply elem_of_mapset_dom_with. rewrite H1; eauto. Qed.

  Lemma singleton_mmtr_connected g x
        (nm : marked g = ∅)
    : connected (<[x := (true, (None, None))]> g) (λ m, m) x.
  Proof.
    intros w b ? ? H1 H2.
    destruct (decide (x = w)); subst.
    - econstructor; eauto.
    - rewrite lookup_insert_ne in H1; eauto.
      destruct b; inversion H2.
      assert (H3 : w ∈ marked g) by (eapply is_marked; eauto).
      rewrite nm in H3; inversion H3.
  Qed.

  Lemma singleton_mmtr_connected_uniquely g x
    : ∀ (y : T) (p p' : Path (<[x:=(true, (None, None))]> g)
                             (λ m : bool, m) x y), p = p'.
  Proof.
    intros w p p'. destruct (decide (x = w)); subst.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + destruct p' as
            [m' l' r' e' Hm' Heq'| z' m' r' p' Hm' Hy' | z' m' r' p' Hm' Hy'].
        * by apply trace_of_ext.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
          inversion p'.
        * exfalso. apply bool_decide_spec in p'. rewrite lookup_insert in p'.
           inversion p'.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p.
    - destruct p as
          [m l r e Hm Heq| z m r p Hm Hy | z m r p Hm Hy].
      + tauto.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p.
      + exfalso. apply bool_decide_spec in p. rewrite lookup_insert in p.
        inversion p.
  Qed.

  Lemma unmarked_maximally_marked g (nm : marked g = ∅)
    : front g (marked g) ⊆ marked g.
  Proof.
    apply elem_of_subseteq => x H1. apply elem_of_front in H1.
    destruct H1 as (H1 & y & m & l & r & H2 & H3 & H4).
    rewrite nm in H2; inversion H2.
  Qed.

  Lemma singleton_mmtr_maximally_marked g x u
        (Hgx : (g !! x = Some (false, u)))
        (nm : marked g = ∅)
    :
      front (<[x:=(true, (None, None))]> g)
            (marked (<[x:=(true, (None, None))]> g))
          ⊆ marked (<[x:=(true, (None, None))]> g).
  Proof.
    rewrite front_insert; eauto.
    - apply elem_of_subseteq => z.
      rewrite marked_insert ?elem_of_union; auto.
      rewrite ?elem_of_singleton.
      intros [[H1 | H1]| H1]; try (inversion H1; fail).
      right; apply unmarked_maximally_marked; eauto.
    - rewrite Hgx; trivial.
  Qed.

  Lemma singleton_maximal_marked_trees g x u
        (Hg1x : (g !! x = Some (false, u)))
        (nm : marked g = ∅)
    : maximal_marked_tree (<[x := (true, (None, None))]> g) x.
  Proof.
    repeat constructor.
    - by eapply singleton_mmtr_connected.
    - by eapply singleton_mmtr_connected_uniquely.
    - by eapply singleton_mmtr_maximally_marked.
  Qed.

  Lemma maximally_marked_end_path_marked g g' z y
        (Hg : ∀ x l r,
            g' !! x = Some (false, (l, r)) → g !! x = Some (false, (l, r)))
        (zm : z ∈ marked g')
        (fg : front g (marked g') ⊆ (marked g'))
        (p : Path g (λ m, true) z y)
    : y ∈ marked g'.
  Proof.
    induction p as
        [x y m l r e Hm Heq | x y z m r Hy Hm p IHp | x y z m l Hy Hm p IHp];
      subst; try apply bool_decide_spec in Hy.
    - auto.
    - apply IHp, fg, elem_of_front; eauto 10 using Path_dom.
    - apply IHp, fg, elem_of_front; eauto 10 using Path_dom.
  Qed.

  Lemma Path_cond_conv g (P Q : bool → bool) x y :
    (∀ b, P b → Q b) → Path g P x y → Path g Q x y.
  Proof.
    intros H p.
    induction p; eauto using Path.
  Qed.

  Lemma Path_cond_conv' g (P Q : bool → bool) x y
        (Hcnv : ∀ x m v, g !! x = Some (m, v) → P m → Q m)
        (p : Path g P x y)
    : {q : Path g Q x y | trace_of p = trace_of q}.
  Proof.
    induction p as
        [x y m l r e Hm Heq | x y z m r Hy Hm p IHp | x y z m l Hy Hm p IHp];
      subst; try (set (Hy' := proj1 (bool_decide_spec _) Hy); clearbody Hy').
    - eexists (Path_O _ _ _ _ _ _ _ e _ _); eauto.
      Unshelve. all: eauto.
    - destruct IHp as [q Hq].
      eexists (Path_Sl _ _ _ _ _ _ _ _ _ q).
      + by cbn; rewrite Hq.
        Unshelve. all: eauto.
    - destruct IHp as [q Hq].
      eexists (Path_Sr _ _ _ _ _ _ _ _ _ q).
      + by cbn; rewrite Hq.
        Unshelve. all: eauto.
  Qed.

  Lemma maximally_marked_dom_marked g g' z
        (Hg : ∀ x l r,
            g' !! x = Some (false, (l, r)) → g !! x = Some (false, (l, r)))
        (cn : connected g (λ _, true) z)
        (zm : z ∈ marked g')
        (fg : front g (marked g') ⊆ (marked g'))
    : dom (gset _) g ⊆ marked g'.
  Proof.
    apply elem_of_subseteq => x H1.
    eapply (maximally_marked_end_path_marked g); eauto.
    apply elem_of_dom in H1; unfold is_Some in H1. unfold graph in *.
    destruct (g !! x) as [[? [? ?]]|] eqn:Heq.
    eapply cn; eauto.
    exfalso; destruct H1 as [? H1]; inversion H1.
  Qed.

  Lemma dom_marked_all_convertible_to_marked g
        (Hd : dom (gset _) g ⊆ marked g)
    : ∀ x (m : bool) v, g !! x = Some (m, v) → true → m.
  Proof.
    intros x m v H1 _.
    set (Hd' := proj1 (elem_of_subseteq _ _) Hd); clearbody Hd'.
    specialize (Hd' x). revert Hd'.
    rewrite elem_of_dom /is_Some /marked elem_of_mapset_dom_with => Hd'.
    unfold graph in *. destruct (g !! x); inversion H1; subst.
    edestruct Hd' as [z [H21 H22]]; eauto.
    destruct m; cbn; trivial.
    inversion H21; subst; inversion H22.
  Qed.

  Hint Resolve dom_marked_all_convertible_to_marked.

  Lemma maximally_marked_tree_marked_dom_gives_tree g z
        (mtr : maximal_marked_tree g z)
        (Hd : dom (gset _) g ⊆ marked g)
    : tree g (λ x, true) z.
  Proof.
    destruct mtr as [[cn cnu] mm].
    set (Hd' := proj1 (elem_of_subseteq _ _) Hd); clearbody Hd'.
    unfold marked in Hd'.
    constructor.
    - intros w m l r H1 H2.
      eapply Path_cond_conv; [|eapply cn]; eauto.
    - intros y p p'. apply trace_of_ext.
      edestruct (λ H, Path_cond_conv' _ _ (λ m, m) _ _ H p) as [q Hq]; eauto.
      edestruct (λ H, Path_cond_conv' _ _ (λ m, m) _ _ H p') as [q' Hq'];
        eauto.
      by rewrite Hq Hq' (cnu _ q q').
  Qed.

End Graphs.

Arguments graph _ {_ _}, {_ _ _}.