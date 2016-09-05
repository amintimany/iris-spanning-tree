From iris.algebra Require Import frac dec_agree gmap upred_big_op.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre tactics.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Export lifting heap notation.
From iris.heap_lang.lib Require Import par.
From iris.program_logic Require Import cancelable_invariants.
Import uPred.

From iris_spanning_tree Require Import graph mon.

Definition try_mark : val :=
  λ: "y", let: "e" := Fst (!"y") in CAS "e" #false #true.

Definition unmark_fst : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (Fst "e", (NONE, Snd (Snd "e"))).

Definition unmark_snd : val :=
  λ: "y",
  let: "e" := ! "y" in "y" <- (Fst "e", (Fst (Snd "e"), NONE)).

Definition span : val :=
  rec: "span" "x" :=
  match: "x" with
    NONE => # false
  | SOME "y" =>
    if: try_mark "y" then
      let: "e" := ! "y" in
      let: "rs" := "span" (Fst (Snd "e")) || "span" (Snd (Snd "e")) in
      ((if: ~ (Fst "rs") then unmark_fst "y" else #())
         ;; if: ~ (Snd "rs") then unmark_snd "y" else #());; #true
    else
      #false
  end.

Section Helpers.
  Context `{heapG Σ, cinvG Σ, graphG Σ, spawnG Σ} (κ : gname).

  Lemma wp_try_mark g Mrk k q (x : loc) : x ∈ dom (gset _) g →
    heap_ctx ★ graph_ctx κ g Mrk ★ own_graph q ∅ ★ cinv_own κ k
    ⊢ WP (try_mark #x) {{ v,
         (v = #true ★ (∃ u, (g !! x) = Some u ★ own_graph q (x [↦] u))
          ★ is_marked x ★ cinv_own κ k)
           ∨ (v = #false ★ own_graph q ∅ ★ is_marked x ★ cinv_own κ k)
      }}.
  Proof.
    iIntros (Hgx) "(#Hheap & #Hgr & Hx & key)". unfold try_mark.
    wp_let; wp_bind (! _)%E. unfold graph_ctx.
    iVs (cinv_open with "Hgr key") as "(>Hinv & key & Hcl)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G mr) "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u) "[Hil1 Hil2]".
    iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load.
    iDestruct "Hil1" as %Hil1. iDestruct "Hil2" as %Hil2.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3"; eauto.
    { iFrame. iExists _; eauto. iSplitR; eauto. iExists _; by iFrame. }
    iVs ("Hcl" with "[Hi1 Hi2 Hi3 Hi5 Hi4]") as "_".
    { iNext. unfold graph_inv at 2. iExists _, _; iFrame; auto. }
    iVsIntro.
    destruct u as [u1 u2]; simpl. wp_bind (Fst _). iApply wp_fst; eauto.
    { rewrite children_to_val_is_val; eauto. }
    iNext; iVsIntro; wp_let.
    iVs (cinv_open _ graphN with "Hgr key")
      as "(>Hinv & key & Hclose)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G' mr') "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u) "[Hil1 Hil2]".
    iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    iDestruct "Hil2" as %Hil2'. iDestruct "Hil1" as %Hil1'.
    iDestruct "Hi5" as %Hi5. iDestruct "Hi4" as %Hi4.
    rewrite Hil2' in Hil2; inversion Hil2; subst.
    iDestruct (auth_own_graph_valid with "#Hi1") as %Hvl.
    destruct u as [[] uch].
    - wp_cas_fail; first done.
      iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3";
      eauto.
      { iFrame. iExists _; eauto. iSplitR; eauto. by iExists _; iFrame. }
      iVs (already_marked with "Hi2") as "[Hi2 Hxm]"; [|iFrame "Hxm"].
      { rewrite Hi4. by eapply in_dom_of_graph. }
      iVs ("Hclose" with "[Hi1 Hi2 Hi3]") as "_".
      { iNext. unfold graph_inv at 2. iExists _, _; iFrame; auto. }
      iVsIntro. iFrame. iRight; by iFrame.
    - (* CAS succeeds *)
      wp_cas_suc; first done.
      iVs (mark_graph _ _ x uch with "[Hi1 Hx]") as "[Hi1 Hx]"; try by iFrame.
      { apply (proj1 (not_elem_of_dom (D := gset loc) G' x)).
        intros Hid. eapply in_dom_of_graph in Hid; eauto; tauto. }
      iVs (new_marked with "Hi2") as "[Hi2 Hm]". iFrame "key Hm".
      erewrite delete_marked.
      iDestruct (auth_own_graph_valid with "#Hi1") as %Hvl'.
      iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
      { iFrame. iExists (_, _). iSplitR; [| iExists _; iFrame]; trivial.
          rewrite mark_update_lookup; eauto. }
      iVs ("Hclose" with "[Hi1 Hi2 Hi3]") as "_".
      + iNext; unfold graph_inv at 2. iExists _, _; iFrame.
        repeat iSplit; iPureIntro.
        { by rewrite ?dom_op ?dom_singleton_L Hi4 comm_L. }
        { by apply mark_strict_subgraph. }
      + iVsIntro. iLeft; iSplit; trivial. iExists _; iFrame.
        iPureIntro; eapply of_graph_unmarked; eauto.
  Qed.

  Lemma laod_strict_sub_children g G x w u : g !! x = Some u →
    strict_subgraph g (Gmon_graph ((x [↦] w) ⋅ delete x G)) →
    strict_sub_children u w.
  Proof.
    move => Hgx /(_ x).
    rewrite /get_left /get_right /Gmon_graph Hgx ?lookup_omap ?lookup_op
      ?lookup_delete ?right_id_L ?lookup_singleton /=;
      destruct w; destruct u; done.
  Qed.

  Lemma wp_load_graph g markings k q (x : loc) u w :
    (g !! x) = Some u →
    (heap_ctx ★ graph_ctx κ g markings ★ own_graph q (x [↦] w) ★ cinv_own κ k)
      ⊢
      WP (! #x)
      {{ v, (∃ m : loc, (markings !! x) = Some m ∧
              v = (#m, children_to_val w)%V) ★ ■ strict_sub_children u w
              ★ own_graph q (x [↦] w) ★ cinv_own κ k }}.
  Proof.
    iIntros (Hgx) "(#Hheap & #Hgr & Hx & key)".
    assert (Hgx' : x ∈ dom (gset _) g).
    { rewrite elem_of_dom Hgx; eauto. }
    unfold graph_ctx.
    iVs (cinv_open _ graphN with "Hgr key")
      as "(>Hinv & key & Hclose)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G mr) "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u') "[Hil1 Hil2]".
    iDestruct "Hil2" as (m) "[Hil2 [Hil3 Hil4]]".
    wp_load. iDestruct "Hi5" as %Hi5. iDestruct "Hil1" as %Hil1.
    iDestruct "Hil2" as %Hil2. iDestruct "Hi4" as %Hi4.
    iDestruct (auth_own_graph_valid with "#Hi1") as %Hvl.
    iDestruct (graph_pointsto_marked with "[#]")
      as %Heq; try by iFrame.
    pose proof Hil1 as Hil1'. rewrite Heq in Hil1' Hvl.
    rewrite mark_update_lookup in Hil1'; trivial.
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3"; [iFrame|].
    { iExists _; iSplitR; auto. iExists _; by iFrame. }
    iVs ("Hclose" with "[Hi1 Hi2 Hi3]") as "_".
    { iNext. unfold graph_inv at 2. iExists _, _; iFrame; auto. }
    iFrame. inversion Hil1'; subst u'; simpl.
    iVsIntro. iSplit; [|iPureIntro]. iExists _; iSplit; iPureIntro; eauto.
    { rewrite Heq in Hi5. eapply laod_strict_sub_children; eauto. }
  Qed.

  Lemma wp_store_graph {g markings k q} {x : loc} {v}
        (w w' : option loc * option loc) {m : loc} :
    strict_sub_children w w' → (markings !! x) = Some m →
      (g !! x) = Some v →
      (heap_ctx ★ graph_ctx κ g markings ★ own_graph q (x [↦] w) ★ cinv_own κ k)
        ⊢
        WP (#x <- (#m, children_to_val w'))
        {{ v, own_graph q (x [↦] w') ★ cinv_own κ k }}.
  Proof.
    iIntros (Hagree Hmrk Hgx) "(#Hheap & #Hgr & Hx & key)".
    assert (Hgx' : x ∈ dom (gset _) g).
    { rewrite elem_of_dom Hgx; eauto. }
    unfold graph_ctx.
    iVs (cinv_open _ graphN with "Hgr key")
      as "(>Hinv & key & Hclose)"; first done.
    unfold graph_inv at 2.
    iDestruct "Hinv" as (G mr) "(Hi1 & Hi2 & Hi3 & Hi4 & Hi5)".
    iDestruct (graph_open with "[Hi1 Hi3]") as
        "(Hi1 & Hi3 & Hil)"; eauto; [by iFrame|].
    iDestruct "Hil" as (u') "[Hil1 Hil2]".
    iDestruct "Hil2" as (m') "[Hil2 [Hil3 Hil4]]".
    wp_store.
    iDestruct "Hil2" as %Hil2.
    rewrite Hmrk in Hil2. inversion Hil2; subst; clear Hil2.
    iDestruct "Hil1" as %Hil1. iDestruct "Hi4" as %Hi4. iDestruct "Hi5" as %Hi5.
    iDestruct (auth_own_graph_valid with "#Hi1") as %Hvl.
    iDestruct (graph_pointsto_marked with "[#]") as %Heq; try by iFrame.
    pose proof Hil1 as Hil1'. rewrite Heq in Hil1' Hvl Hi5.
    rewrite mark_update_lookup in Hil1'; trivial. inversion Hil1'; subst u'.
    clear Hil1'. simpl. rewrite Heq.
    iVs (update_graph _ _ _ w' with "[Hi1 Hx]") as
        "[Hi1 Hx]"; try by iFrame. by rewrite lookup_delete.
    rewrite -delete_marked. erewrite (delete_marked _ _ _ w').
    assert (HvG : ✓ ({[x := Excl w']} ⋅ delete x G)).
    { eapply update_valid; eauto. }
    iDestruct (graph_close with "[Hi3 Hil3 Hil4]") as "Hi3".
    { iFrame. iExists _. iSplitR.
      - rewrite ?mark_update_lookup; eauto. - iExists _; by iFrame. }
    iVs ("Hclose" with "[Hi1 Hi2 Hi3]") as "_"; [|by iFrame].
    unfold graph_inv at 2.
    iNext. iExists _, _; iFrame. repeat iSplit; iPureIntro.
    { rewrite Heq in Hi4. rewrite Hi4 ?dom_op ?dom_singleton_L; trivial. }
    { eapply update_strict_subgraph; eauto. }
  Qed.

  Lemma wp_unmark_fst g markings k q (x : loc) v w1 w2 :
    (g !! x) = Some v →
    (heap_ctx ★ graph_ctx κ g markings ★ own_graph q (x [↦] (w1, w2))
     ★ cinv_own κ k) ⊢
      WP (unmark_fst #x)
      {{ _, own_graph q (x [↦] (None, w2)) ★ cinv_own κ k }}.
  Proof.
    iIntros (Hgx) "(#Hheap & #Hgr & Hx & key)". unfold unmark_fst.
    wp_let. wp_bind (! _)%E.
    iApply wp_wand_l; iSplitR;
      [|iApply wp_load_graph; eauto; iFrame "Hheap Hgr"; by iFrame].
    iIntros (u) "(H1 & Hagree & Hx & key)". iDestruct "H1" as (m) "[Hmrk Hu]".
    iDestruct "Hagree" as %Hagree.
    iDestruct "Hmrk" as %Hmrk; iDestruct "Hu" as %Hu; subst.
    wp_let. wp_bind (Fst _). iApply wp_fst; eauto.
    { rewrite children_to_val_is_val ; eauto. }
    iNext; iVsIntro. wp_bind (Snd (_, _)). iApply wp_snd; eauto.
    { by rewrite children_to_val_is_val. }
    iNext; iVsIntro. wp_bind (Snd _). iApply wp_snd; eauto.
    { rewrite to_of_val; eauto. }
    {by rewrite to_of_val. }
    iNext. iVsIntro.
    iApply (wp_store_graph _ (None, w2) with "[Hx key]"); eauto;
      [|iFrame "Hheap Hgr"; by iFrame].
    { by destruct w1; destruct w2; destruct v; inversion Hagree; subst. }
  Qed.

  Lemma wp_unmark_snd g markings k q (x : loc) v w1 w2 :
    (g !! x) = Some v →
    (heap_ctx ★ graph_ctx κ g markings ★ own_graph q (x [↦] (w1, w2))
     ★ cinv_own κ k) ⊢
      WP (unmark_snd #x)
      {{ _, own_graph q (x [↦] (w1, None)) ★ cinv_own κ k }}.
  Proof.
    iIntros (Hgx) "(#Hheap & #Hgr & Hx & key)". unfold unmark_fst.
    wp_let. wp_bind (! _)%E.
    iApply wp_wand_l; iSplitR;
      [|iApply wp_load_graph; eauto; iFrame "Hheap Hgr"; by iFrame].
    iIntros (u) "(H1 & Hagree & Hx & key)". iDestruct "H1" as (m) "[Hmrk Hu]".
    iDestruct "Hagree" as %Hagree.
    iDestruct "Hmrk" as %Hmrk; iDestruct "Hu" as %Hu; subst.
    wp_let. wp_bind (Fst _). iApply wp_fst; eauto.
    { rewrite children_to_val_is_val; eauto. }
    iNext; iVsIntro. wp_bind (Snd (_, _)). iApply wp_snd; eauto.
    { by rewrite children_to_val_is_val. }
    iNext; iVsIntro. wp_bind (Fst _). iApply wp_fst; eauto.
    {by rewrite to_of_val. }
    { rewrite to_of_val; eauto. }
    iNext. iVsIntro.
    iApply (wp_store_graph _ (w1, None) with "[Hx key]"); eauto;
      [|iFrame "Hheap Hgr"; by iFrame].
    { by destruct w1; destruct w2; destruct v; inversion Hagree; subst. }
  Qed.

  Typeclasses Opaque try_mark unmark_fst unmark_snd.
  Global Opaque try_mark unmark_fst unmark_snd.
(*
  Inductive weak_path (g : graph loc) (x y : loc) :=
  | WPO : x = y → weak_path g x y
  | WPSl b l r : g !! x = Some (b, (Some l, r)) → weak_path g l y
                 → weak_path g x y
  | WPSr b l r : g !! x = Some (b, (l, Some r)) → weak_path g r y →
                 weak_path g x y.

  Definition self_contained (g : graph loc) x :=
    x ∈ dom (gset _) g ∧ (∀ y, weak_path g x y → y ∈ dom (gset _) g).

  Definition self_contained_in_dom (g : graph loc) x :
    self_contained g x → x ∈ dom (gset _) g.
  Proof. by intros [? ?]. Qed.

  Hint Resolve self_contained_in_dom.

  Lemma self_contained_l g x b w1 w2:
    self_contained g x → g !! x = Some (b, (Some w1, w2)) → self_contained g w1.
  Proof.
    intros Hgsl Hgx. split.
    - apply Hgsl; econstructor 2; eauto; constructor 1; eauto.
    - intros y Hwp. apply Hgsl. econstructor 2; eauto.
  Qed.

  Hint Resolve self_contained_l.

  Lemma self_contained_r g x b w1 w2:
    self_contained g x → g !! x = Some (b, (w1, Some w2)) → self_contained g w2.
  Proof.
    intros Hgsl Hgx. split.
    - apply Hgsl; econstructor 3; eauto; constructor 1; eauto.
    - intros y Hwp. apply Hgsl. econstructor 3; eauto.
  Qed.

  Hint Resolve self_contained_r.

  Lemma empty_graph_divide q :
    Γρ(q, ∅) ⊢ Γρ((q / 2)%Qp, ∅) ★ Γρ((q / 2)%Qp, ∅).
  Proof.
    setoid_replace (∅ : gmapR loc (exclR chlC)) with
    (∅ ⋅ ∅ : gmapR loc (exclR chlC)) at 1 by (by rewrite ucmra_unit_left_id).
    by rewrite graph_divide.
  Qed.

  Local Hint Resolve of_graph_marked_disjoint of_graph_agree_unmarked
        cmra_valid_op_r cmra_valid_op_l.

  Local Hint Extern 1 =>
  match goal with
    |- context [dom (gset _) (of_graph _ _)] => rewrite ?of_graph_dom
  end.

  Lemma maximally_marked_lr {g : graph loc}
        {γ1 γ2 : gmapR loc (exclR chlC)} {l u1 u2} {l1 l2 : loc}
        {Hgsl : self_contained g l} {Hgnm : marked g = ∅}
        {Hvl : ✓ ({[l := Excl (u1, u2)]} ⋅ (γ1 ⋅ γ2))}
        {Hgl : g !! l = Some (false, (u1, u2))}
        {Hl1eq : opl_heap u1 = SOMEV #l1} {Hl2eq : opl_heap u2 = SOMEV #l2}
        {Hl1m : l1 ∈ marked (of_graph g γ1)}{Hl2m : l2 ∈ marked (of_graph g γ2)}
        (mmr1 : maximal_marked_tree (of_graph g γ1) l1)
        (mmr2 : maximal_marked_tree (of_graph g γ2) l2)
    :
      maximal_marked_tree
        (of_graph g ({[l := Excl (u1, u2)]} ⋅ (γ1 ⋅ γ2))) l.
  Proof.
    rewrite of_graph_singleton_op //= ?elem_of_dom; eauto.
    rewrite of_graph_op_combine; eauto.
    destruct u1; destruct u2; inversion Hl1eq; inversion Hl2eq; subst.
    apply combine_maximal_marked_trees_both; trivial; eauto 6.
    - erewrite of_graph_op_singleton_unmarked; auto.
      + eapply cmra_valid_op_l; rewrite -assoc; eauto.
    - erewrite of_graph_op_singleton_unmarked; auto.
      + eapply cmra_valid_op_l; rewrite -assoc (cmra_comm γ2); eauto.
  Qed.

  Lemma unmarked_conv (g : graph loc) l :
    l ∈ dom (gset _) g → l ∉ marked g →
    match g !! l with
    | Some (m, _) => m = false
    | None => False
    end.
  Proof.
    rewrite /marked elem_of_dom mapset.elem_of_mapset_dom_with.
    intros [[[] ?] Hx]; rewrite Hx; trivial.
    intros Hy; exfalso; apply Hy; eauto.
  Qed.

  Lemma front_marked_lr (g : graph loc)
        {γ1 γ2 : gmapR loc (exclR chlC)} {l u1 u2} {l1 l2 : loc}
        {Hgsl : self_contained g l} {Hgnm : marked g = ∅}
        {Hvl : ✓ ({[l := Excl (u1, u2)]} ⋅ (γ1 ⋅ γ2))}
        {Hgl : g !! l = Some (false, (u1, u2))}
        {Hl1eq : opl_heap u1 = SOMEV #l1} {Hl2eq : opl_heap u2 = SOMEV #l2}
        {Hl1m : l1 ∈ marked (of_graph g γ1)}{Hl2m : l2 ∈ marked (of_graph g γ2)}
    :
      μ(l1) ★ μ(l2)
       ★ ([★ set] l ∈ (front g (marked (of_graph g γ1))) , μ(l))
       ★ ([★ set] l ∈ (front g (marked (of_graph g γ2))) , μ(l))
       ⊢ ([★ set] l ∈ front g
                  (marked (of_graph g ({[l := Excl (u1, u2)]} ⋅ (γ1 ⋅ γ2))))
          , μ(l)).
  Proof.
    assert (Hvl1 : ✓ ({[l := Excl (u1, u2)]} ⋅ γ1)).
    { revert Hvl; rewrite assoc; eauto. }
    assert (Hvl2 : ✓ ({[l := Excl (u1, u2)]} ⋅ γ2)).
    { revert Hvl; rewrite (cmra_comm γ1) assoc; eauto. }
    iIntros "(Hl1 & Hl2 & Hsl1 & Hsl2)".
    rewrite ?big_sepS_forall. iIntros (z Hz).
    rewrite ?of_graph_singleton_op //= ? elem_of_dom in Hz; eauto.
    rewrite ?of_graph_op_combine in Hz; eauto using cmra_valid_op_r.
    destruct u1; destruct u2; inversion Hl1eq; inversion Hl2eq; subst.
    revert Hz.
    rewrite marked_insert combine_graphs_marked_eq_union ?front_of_union
            ?elem_of_union; eauto.
    intros [Hz|[Hz|Hz]]; try (iApply "Hsl1" + iApply "Hsl2"; by eauto).
    revert Hz; rewrite elem_of_front.
    intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
      revert Hz2; rewrite elem_of_singleton; intros Hz2;
        subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
  Qed.

  Lemma maximally_marked_l (g : graph loc)
        (γ1 : gmapR loc (exclR chlC)) l u1 u2 (l1 : loc)
        (Hgsl : self_contained g l) (Hgnm : marked g = ∅)
        (Hvl : ✓ ({[l := Excl (u1, None)]} ⋅ γ1))
        (Hgl : g !! l = Some (false, (u1, u2)))
        (Hl1eq : opl_heap u1 = SOMEV #l1)
        (Hl1m : l1 ∈ marked (of_graph g γ1))
        (mmr1 : maximal_marked_tree (of_graph g γ1) l1)
    :
      maximal_marked_tree
        (of_graph g ({[l := Excl (u1, None)]} ⋅ γ1)) l.
  Proof.
    rewrite of_graph_singleton_op //= ?elem_of_dom; eauto.
    destruct u1; inversion Hl1eq; subst.
    eapply left_maximal_marked_trees; eauto.
    erewrite of_graph_op_singleton_unmarked; eauto.
  Qed.

  Lemma front_marked_l (g : graph loc)
        (γ1: gmapR loc (exclR chlC)) l u1 u2 (l1 : loc)
        (Hgsl : self_contained g l) (Hgnm : marked g = ∅)
        (Hvl : ✓ ({[l := Excl (u1, None)]} ⋅ γ1))
        (Hgl : g !! l = Some (false, (u1, u2)))
        (Hl1eq : opl_heap u1 = SOMEV #l1)
        (Hl1m : l1 ∈ marked (of_graph g γ1))
    :
      μ(l1) ★ (opl_heap u2 = NONEV ∨
               (∃ l' : loc, opl_heap u2 = SOMEV #l' ★ μ(l')))
       ★ ([★ set] l ∈ (front g (marked (of_graph g γ1))) , μ(l))
       ⊢ ([★ set] l ∈ front g
                  (marked (of_graph g ({[l := Excl (u1, None)]} ⋅ γ1)))
          , μ(l)).
  Proof.
    destruct u1; inversion Hl1eq; subst.
    iIntros "(Hl1 &Hl2 & Hsl2)".
    rewrite ?big_sepS_forall. iIntros (z Hz).
    rewrite ?of_graph_singleton_op //= ? elem_of_dom in Hz; eauto.
    revert Hz.
    rewrite marked_insert ?front_of_union ?elem_of_union; eauto.
    intros [Hz|Hz]; try (iApply "Hsl2"; by eauto).
    iDestruct "Hl2" as "[Hl2|Hl2]".
    - iDestruct "Hl2" as %Hl2. destruct u2; inversion Hl2.
    revert Hz; rewrite elem_of_front.
    intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
      revert Hz2; rewrite elem_of_singleton => Hz2; subst; rewrite Hgl in Hz3;
                                                inversion Hz3; subst; trivial.
    - iDestruct "Hl2" as (l2) "[Hl2eq Hl2]".
      iDestruct "Hl2eq" as %Hl2eq. destruct u2; inversion Hl2eq.
      revert Hz; rewrite elem_of_front.
      intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
        revert Hz2; rewrite elem_of_singleton; intros Hz2;
          subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
  Qed.

  Lemma maximally_marked_r (g : graph loc)
        (γ2 : gmapR loc (exclR chlC)) l u1 u2 (l2 : loc)
        (Hgsl : self_contained g l) (Hgnm : marked g = ∅)
        (Hvl : ✓ ({[l := Excl (None, u2)]} ⋅ γ2))
        (Hgl : g !! l = Some (false, (u1, u2)))
        (Hl2eq : opl_heap u2 = SOMEV #l2)
        (Hl2m : l2 ∈ marked (of_graph g γ2))
        (mmr2 : maximal_marked_tree (of_graph g γ2) l2)
    :
      maximal_marked_tree
        (of_graph g ({[l := Excl (None, u2)]} ⋅ γ2)) l.
  Proof.
    rewrite of_graph_singleton_op //= ?elem_of_dom; eauto.
    destruct u2; inversion Hl2eq; subst.
    eapply right_maximal_marked_trees; eauto.
    erewrite of_graph_op_singleton_unmarked; eauto.
  Qed.

  Lemma front_marked_r (g : graph loc)
        (γ2 : gmapR loc (exclR chlC)) l u1 u2 (l2 : loc)
        (Hgsl : self_contained g l) (Hgnm : marked g = ∅)
        (Hvl : ✓ ({[l := Excl (None, u2)]} ⋅ γ2))
        (Hgl : g !! l = Some (false, (u1, u2)))
        (Hl2eq : opl_heap u2 = SOMEV #l2)
        (Hl2m : l2 ∈ marked (of_graph g γ2))
    :
      (opl_heap u1 = NONEV ∨
       (∃ l' : loc, opl_heap u1 = SOMEV #l' ★ μ(l'))) ★ μ(l2)
       ★ ([★ set] l ∈ (front g (marked (of_graph g γ2))) , μ(l))
       ⊢ ([★ set] l ∈ front g
                  (marked (of_graph g ({[l := Excl (None, u2)]} ⋅ γ2)))
          , μ(l)).
  Proof.
    destruct u2; inversion Hl2eq; subst.
    iIntros "(Hl1 &Hl2 & Hsl1)".
    rewrite ?big_sepS_forall. iIntros (z Hz).
    rewrite ?of_graph_singleton_op //= ? elem_of_dom in Hz; eauto.
    revert Hz.
    rewrite marked_insert ?front_of_union ?elem_of_union; eauto.
    intros [Hz|Hz]; try (iApply "Hsl1"; by eauto).
    iDestruct "Hl1" as "[Hl1|Hl1]".
    - iDestruct "Hl1" as %Hl1. destruct u1; inversion Hl1.
    revert Hz; rewrite elem_of_front.
    intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
      revert Hz2; rewrite elem_of_singleton => Hz2; subst; rewrite Hgl in Hz3;
                                                inversion Hz3; subst; trivial.
    - iDestruct "Hl1" as (l1) "[Hl1eq Hl1]".
      iDestruct "Hl1eq" as %Hl1eq. destruct u1; inversion Hl1eq.
      revert Hz; rewrite elem_of_front.
      intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
        revert Hz2; rewrite elem_of_singleton; intros Hz2;
          subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
  Qed.

  Lemma maximally_marked_none (g : graph loc)
        l u1 u2
        (Hgnm : marked g = ∅)
        (Hvl : ✓ (({[l := Excl (None, None)]} ⋅ ∅) : gmapR loc (exclR chlC)))
        (Hgl : g !! l = Some (false, (u1, u2)))
    :
      maximal_marked_tree
        (of_graph g ({[l := Excl (None, None)]} ⋅ ∅)) l.
  Proof.
    rewrite of_graph_singleton_op //= ?elem_of_dom; eauto.
    assert (Hg : of_graph g ∅ = g).
    { rewrite -(to_unmarked_graph g) //= from_to_graph //=. }
    eapply singleton_maximal_marked_trees; rewrite Hg; eauto.
  Qed.

  Lemma front_marked_none (g : graph loc)
        l u1 u2
        (Hgsl : self_contained g l) (Hgnm : marked g = ∅)
        (Hvl : ✓ (({[l := Excl (None, None)]} ⋅ ∅) : gmapR loc (exclR chlC)))
        (Hgl : g !! l = Some (false, (u1, u2)))
    :
      (opl_heap u1 = NONEV ∨
       (∃ l' : loc, opl_heap u1 = SOMEV #l' ★ μ(l')))
        ★
        (opl_heap u2 = NONEV ∨
         (∃ l' : loc, opl_heap u2 = SOMEV #l' ★ μ(l')))
       ⊢ ([★ set] l ∈ front g
                  (marked (of_graph g ({[l := Excl (None, None)]} ⋅ ∅)))
          , μ(l)).
  Proof.
    iIntros "(Hl1 &Hl2)".
    rewrite ?big_sepS_forall. iIntros (z Hz).
    rewrite ?of_graph_singleton_op //= ? elem_of_dom in Hz; eauto.
    revert Hz.
    rewrite marked_insert ?front_of_union ?elem_of_union; eauto.
    intros [Hz|Hz].
    - iDestruct "Hl1" as "[Hl1|Hl1]".
      + iDestruct "Hl1" as %Hl1. destruct u1; inversion Hl1.
        iDestruct "Hl2" as "[Hl2|Hl2]".
        * iDestruct "Hl2" as %Hl2. destruct u2; inversion Hl2.
          revert Hz; rewrite elem_of_front.
          intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
            revert Hz2; rewrite elem_of_singleton; intros Hz2;
              subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
        * iDestruct "Hl2" as (l1) "[Hl2eq Hl2]".
        iDestruct "Hl2eq" as %Hl2eq. destruct u2; inversion Hl2eq.
        revert Hz; rewrite elem_of_front.
        intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
          revert Hz2; rewrite elem_of_singleton; intros Hz2;
            subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
      + iDestruct "Hl1" as (l1) "[Hl1eq Hl1]".
        iDestruct "Hl1eq" as %Hl1eq. destruct u1; inversion Hl1eq.
        iDestruct "Hl2" as "[Hl2|Hl2]".
        * iDestruct "Hl2" as %Hl2. destruct u2; inversion Hl2.
          revert Hz; rewrite elem_of_front.
          intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
            revert Hz2; rewrite elem_of_singleton; intros Hz2;
              subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
        * iDestruct "Hl2" as (l2) "[Hl2eq Hl2]".
          iDestruct "Hl2eq" as %Hl2eq. destruct u2; inversion Hl2eq.
          revert Hz; rewrite elem_of_front.
          intros [Hz1 (y & m & lf & rg & Hz2 & Hz3 & [Hz4|Hz4])];
            revert Hz2; rewrite elem_of_singleton; intros Hz2;
              subst; rewrite Hgl in Hz3; inversion Hz3; subst; trivial.
    - assert (Hg : of_graph g ∅ = g).
      { rewrite -(to_unmarked_graph g) //= from_to_graph //=. }
      rewrite Hg Hgnm in Hz.
      revert Hz. rewrite elem_of_front. intros [? (? & ? & ? & ? & Hemp & ?)].
      inversion Hemp.
  Qed.
*)
(*
  Lemma empty_graph_divide q :
    own_graph q ∅ ⊢ own_graph (q / 2) ∅ ★ own_graph (q / 2) ∅.
  Proof.
    setoid_replace (∅ : gmapR loc (exclR chlC)) with
    (∅ ⋅ ∅ : gmapR loc (exclR chlC)) at 1 by (by rewrite ucmra_unit_left_id).
    by rewrite graph_divide.
  Qed.


  Lemma rec_wp_span g markings k q (x : val) :
    maximal g →
    (x = NONEV ∨ ∃ l : loc,
        x = SOMEV #l ∧ l ∈ dom (gset _) g) →
    (heap_ctx ★ graph_ctx κ g markings ★ own_graph q ∅ ★ cinv_own κ k)
      ⊢
      WP (span x)
      {{ v, ((v = # true ★
             (∃ l : loc, x = SOMEV #l ★
               (∃ (G : Gmon) mr (tr : tree (Gmon_graph G) l),
                  own_graph q G ★ ■ (l ∈ dom (gset _) G) ★
                  ■ maximal (Gmon_graph G) ★ ■ (front g (dom (gset _) G) mr) ★
                   ([★ set] l ∈ mr , is_marked l)) ★ is_marked l)) ∨
             (v = # false ★
              (x = NONEV ∨ (∃ l : loc, x = SOMEV #l ★ is_marked l))
               ★ own_graph q ∅))
            ★ cinv_own κ k
      }}.
  Proof.
    intros [_ Hgmx] Hxpt. iIntros "(#Hheap & #Hgr & Hx & key)".
    iRevert (x Hxpt k q) "key Hx". iLöb as "IH".
    iIntros (x Hxpt k q) "key Hx".
    wp_rec.
    destruct Hxpt as [|[l [? Hgsl]]]; subst.
    { wp_match. iVsIntro.
      iFrame; iRight; iFrame; repeat iSplit; trivial; by iLeft. }
    wp_match. wp_bind (try_mark _).
    iDestruct (empty_graph_divide with "Hx") as "[Hx1 Hx2]".
    iApply wp_wand_l; iSplitL "Hx1";
      [|iApply wp_try_mark; try iFrame]; eauto; simpl.
    iIntros (v) "[(% & Hv & Hm & key)|(% & Hx2 & Hm & key)]"; subst;
    [|iCombine "Hx1" "Hx2" as "Hx"; rewrite -graph_divide ucmra_unit_right_id;
      wp_if; iVsIntro; iFrame; iRight; iFrame; iSplit; trivial; iRight;
      iExists _; eauto].
    iDestruct "Hv" as (u) "[Hgl Hl]". iDestruct "Hgl" as %Hgl.
    wp_if.
    (* reading the reference. This part is very similar to unmark lemmas! *)
    wp_bind (! _)%E.
    iApply wp_wand_l; iSplitR "Hl key";
      [|iApply wp_load_graph; eauto; iFrame "Hheap Hgr"; by iFrame].
    iIntros (v) "(H1 & Hagree & Hx & key)". iDestruct "H1" as (m) "[Hmrk Hv]".
    iDestruct "Hagree" as %Hagree. iDestruct "Hv" as %Hv; subst v.
    wp_let. wp_bind (par _).
    erewrite <- cinv_own_half. iDestruct "key" as "[K1 K2]".
    iDestruct (empty_graph_divide with "Hx1") as "[Hx11 Hx12]".
    destruct u as [u1 u2]. iApply wp_par. iSplitR; [by iFrame "Hheap"|].
    (* symbolically executing the left part of the par. *)
    iSplitL "Hx11 K1".
    wp_bind (Snd _). iApply wp_snd; eauto.
    { by rewrite children_to_val_is_val. }
    iNext; iVsIntro. wp_bind (Fst _). iApply wp_fst.
    { by rewrite to_of_val. }
    { rewrite to_of_val; eauto. }
    iNext; iVsIntro.
    assert (Hlf : (child_to_val u1) = NONEV
                ∨ (∃ l : loc,
                      (child_to_val u1) = SOMEV #l ∧ l ∈ dom (gset _) g)).
    { destruct u1 as [l1|]; [right |by left].
      exists l1; split; trivial. eapply (Hgmx l); rewrite // /get_left Hgl; auto. }
    iApply ("IH" with "[#] * [K1] [Hx11]"); auto.
    (* symbolically executing the left part of the par. *)
    iSplitL "Hx12 K2".
    wp_bind (Snd (_, _)). iApply wp_snd; eauto.
    { by rewrite children_to_val_is_val. }
    iNext; iVsIntro. wp_bind (Snd _). iApply wp_snd.
    { rewrite to_of_val; eauto. }
    { by rewrite to_of_val. }
    iNext; iVsIntro.
    assert (Hrh : (child_to_val u2) = NONEV
                ∨ (∃ l : loc,
                      (child_to_val u2) = SOMEV #l ∧ l ∈ dom (gset _) g)).
    { destruct u2 as [l2|]; [right |by left].
      exists l2; split; trivial. eapply (Hgmx l); rewrite // /get_right Hgl; auto. }
    iApply ("IH" with "[#] * [K2] [Hx12]"); auto.
    iIntros (vl vr) "[[Hvl K1] [Hvr K2]]".
    iCombine "K1" "K2" as "key". rewrite cinv_own_half.
    iNext. wp_let.
    (* We don't need the huge induction hypothesis anymore. *)
    iClear "IH".
    (* separating all four cases *)
    iDestruct "Hvl" as "[[% Hvll]|[% Hvlr]]"; subst;
      iDestruct "Hvr" as "[[% Hvrl]|[% Hvrr]]"; subst.
    - wp_bind (Fst _). iApply wp_fst; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done. iNext; iVsIntro.
      wp_if; wp_seq.
      wp_bind (Snd _). iApply wp_snd; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done.
      iNext; iVsIntro.
      wp_if.
      iDestruct "Hvll" as (l1) "(Hl1eq & Hg1 & ml1)".
      iDestruct "Hg1" as (G1 mr1 tr1) "(Hxl & Hl1im & Hmx1 & Hfr1 & Hfml)".
      iDestruct "Hfr1" as %Hfr1. iDestruct "Hmx1" as %Hmx1.
      iDestruct "Hl1eq" as %Hl1eq. iDestruct "Hl1im" as %Hl1im.
      iDestruct "Hvrl" as (l2) "(Hl2eq & Hg2 & ml2)".
      iDestruct "Hg2" as (G2 mr2 tr2) "(Hxr & Hl2im & Hmx2 & Hfr2 & Hfmlr)".
      iDestruct "Hfr2" as %Hfr2. iDestruct "Hmx2" as %Hmx2.
      iDestruct "Hl2eq" as %Hl2eq. iDestruct "Hl2im" as %Hl2im.
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide.
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      rewrite dup_marked. iDestruct "Hm" as "[Hm1 Hm2]".
      destruct u1; destruct u2; inversion Hl1eq; inversion Hl2eq; subst.
      iVsIntro. iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame.
      iDestruct (own_graph_valid with "#Hx") as %Hvl.
      iExists ({[l := Excl (Some l1, Some l2)]} ⋅ (G1 ⋅ G2)).
      iExists ({[l1]} ∪ {[l2]} ∪ mr1 ∪ mr2).
      unshelve iExists _; [eapply maximally_marked_tree_both; eauto|].
      iFrame. repeat iSplit; try iPureIntro.
      { rewrite dom_op dom_singleton elem_of_union elem_of_singleton; by left. }
      { eapply maximally_marked_tree_both; eauto. }
      {  }
      iApply (front_marked_lr with "*"); eauto; by iFrame.
    - wp_bind (Fst _). iApply wp_fst; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done. iNext; iVsIntro.
      wp_if; wp_seq.
      wp_bind (Snd _). iApply wp_snd; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done.
      iNext; iVsIntro.
      wp_if.
      iDestruct "Hvll" as (l1) "(Hl1eq & Hg1 & ml1)".
      iDestruct "Hg1" as (γ1 mmr1) "[Hxl [Hl1im Hfml]]".
      iDestruct "Hvrr" as "(Hvr & Hxr)".
      iDestruct "Hl1eq" as %Hl1eq. iDestruct "Hl1im" as %Hl1im.
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide ucmra_unit_right_id.
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_snd; eauto; by iFrame "Hgr Hheap"; iFrame].
      iIntros (v) "[Hx key]".
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      rewrite dup_marked. iDestruct "Hm" as "[Hm1 Hm2]".
      wp_value; iVsIntro; wp_seq; iVsIntro.
      iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame.
      iDestruct (own_graph_valid with "Hx") as "[Hx %]".
      iExists ({[l := Excl (u1, None)]} ⋅ γ1).
      unshelve iExists _; [eapply maximally_marked_l; eauto|].
      iFrame. iSplit; [iPureIntro|].
      rewrite of_graph_singleton_op ?marked_insert ?elem_of_union
              ?elem_of_singleton; eauto.
      iApply (front_marked_l with "*"); eauto; by iFrame.
    - wp_bind (Fst _). iApply wp_fst; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done. iNext; iVsIntro.
      wp_if.
      iDestruct "Hvlr" as "(Hvl & Hxl)".
      iDestruct "Hvrl" as (l2) "(Hl2eq & Hg2 & ml2)".
      iDestruct "Hg2" as (γ2 mmr2) "[Hxr [Hl2im Hfmr]]".
      iDestruct "Hl2eq" as %Hl2eq. iDestruct "Hl2im" as %Hl1im.
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide ucmra_unit_left_id.
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_fst; eauto; by iFrame "Hgr Hheap"; iFrame].
      iIntros (v) "[Hx key]".
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      wp_seq.
      wp_bind (Snd _). iApply wp_snd; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done.
      iNext; iVsIntro.
      wp_if.
      rewrite dup_marked. iDestruct "Hm" as "[Hm1 Hm2]".
      iVsIntro.
      iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame.
      iDestruct (own_graph_valid with "Hx") as "[Hx %]".
      iExists ({[l := Excl (None, u2)]} ⋅ γ2).
      unshelve iExists _; [eapply maximally_marked_r; eauto|].
      iFrame. iSplit; [iPureIntro|].
      rewrite of_graph_singleton_op ?marked_insert ?elem_of_union
              ?elem_of_singleton; eauto.
      iApply (front_marked_r with "*"); eauto; by iFrame.
    - iDestruct "Hvlr" as "(Hvl & Hxl)".
      iDestruct "Hvrr" as "(Hvr & Hxr)".
      iCombine "Hxl" "Hxr" as "Hxlr". rewrite -graph_divide ucmra_unit_right_id.
      wp_bind (Fst _). iApply wp_fst; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done. iNext; iVsIntro.
      wp_if.
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_fst; eauto; by iFrame "Hgr Hheap"; iFrame].
      iIntros (v) "[Hx key]".
      wp_seq.
      wp_bind (Snd _). iApply wp_snd; eauto. iNext; iVsIntro.
      wp_bind (UnOp _ _). iApply wp_un_op; try done.
      iNext; iVsIntro.
      wp_if.
      iApply wp_wand_l; iSplitR "Hx key";
        [|iApply wp_unmark_snd; eauto; by iFrame "Hgr Hheap"; iFrame].
      clear v. iIntros (v) "[Hx key]".
      iCombine "Hx" "Hxlr" as "Hx". rewrite -graph_divide.
      wp_seq.
      rewrite dup_marked. iDestruct "Hm" as "[Hm1 Hm2]".
      iVsIntro.
      iFrame; iLeft. iSplit; [trivial|].
      iExists _; iSplit; [trivial|]. iFrame.
      iDestruct (own_graph_valid with "Hx") as "[Hx %]".
      iExists ({[l := Excl (None, None)]} ⋅ ∅).
      unshelve iExists _; [eapply maximally_marked_none; eauto|].
      iFrame. iSplit; [iPureIntro|].
      rewrite of_graph_singleton_op ?marked_insert ?elem_of_union
              ?elem_of_singleton; eauto.
      iApply (front_marked_none with "*"); eauto; by iFrame.
      (* unshelving *)
      Unshelve. all: trivial.
  Qed.

End Helpers.
*)