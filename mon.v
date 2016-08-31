From iris.heap_lang Require Export lifting heap notation.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre ghost_ownership
     tactics invariants.
Import uPred.

From iris.program_logic Require Import cancelable_invariants.

From iris.algebra Require Import base cmra gmap.
From iris.prelude Require Import gmap mapset.

Require Import iris_spanning_tree.graph.

(* Timeless Lemmas for uPred_big_sepM. *)

Local Arguments cmra_op _ !_ !_ / : simpl nomatch.
Local Arguments ucmra_op _ !_ !_ / : simpl nomatch.
Local Arguments op _ _ !_ !_ /.

(* This should be put in iris *)
Lemma None_op {A} (x : optionR A) : None ⋅ x = x.
Proof. by destruct x. Qed.

(* children cofe *)
Canonical Structure chlC := leibnizC (option loc * option loc)%type.
(* The graph monoid. *)
Definition graphN : namespace := nroot .@ "SPT_graph".
Definition graphUR : ucmraT :=
  optionUR (prodR fracR (gmapR loc (exclR chlC))).
(* The monoid for talking about which nodes are marked.
These markings are duplicatable. *)
Definition markingUR : ucmraT := gmapUR loc unitR.

(** The CMRA we need. *)
Class graphG Σ := GraphG
  {
    graph_marking_inG :> authG Σ markingUR;
    graph_marking_name : gname;
    graph_inG :> authG Σ graphUR;
    graph_name : gname
  }.
(** The Functor we need. *)
(*Definition graphΣ : gFunctors := #[authΣ graphUR].*)

Section marking_definitions.
  Context `{irisG heap_lang Σ, graphG Σ}.

  Definition is_marked (l : loc) : iProp Σ :=
    auth_own graph_marking_name ({[ l := () ]} : markingUR).

  Lemma dup_marking (m : markingUR) : m ≡ m ⋅ m.
  Proof.
    intros i. rewrite lookup_op.
    match goal with
      |- ?B ≡ ?A ⋅ ?A => change B with A; by destruct A as [[]|]
    end.
  Qed.

  Notation "'μ(' x )" := (is_marked x) (format "μ( x )").

  Global Instance marked_persistentP x : PersistentP (μ(x)).
  Proof. apply _. Qed.

  Lemma dup_marked l : μ(l) ⊣⊢ μ(l) ★ μ(l).
  Proof. by rewrite /is_marked -auth_own_op -dup_marking. Qed.

  Lemma new_marked_local_update (m m' : markingUR) : ∅ ~l~> m' @ Some m.
  Proof.
    constructor.
    - intros n H1 i; specialize (H1 i); revert H1. simpl.
      rewrite ?lookup_op ?lookup_empty.
      match goal with
        |- ✓{n} (None ⋅ ?A) → ✓{n} (?B ⋅ ?A) =>
        destruct A as [[]|]; destruct B as [[]|]
      end; done.
    - intros n [mz|]; simpl in *; rewrite ?ucmra_unit_left_id => H1 H2.
      + by rewrite H2.
      + by rewrite H2 ucmra_unit_right_id.
  Qed.

  Lemma new_marked_update {m : markingUR} l :
    (● m ⋅ ◯ ∅) ~~> (● (m ⋅ {[l := () ]}) ⋅ ◯ ({[l := () ]})).
  Proof.
    rewrite <- (ucmra_unit_left_id m) at 1.
    rewrite (cmra_comm m).
    apply auth_update, new_marked_local_update.
  Qed.

  Lemma new_marked {E} (m : markingUR) l : own graph_marking_name (● m) ⊢ |={E}=>
  own graph_marking_name (● (m ⋅ {[l := () ]})) ★ μ(l).
  Proof.
    iIntros "H1".
    iVs (auth_empty (A := markingUR) graph_marking_name) as "H2".
    unfold auth_own. iCombine "H1" "H2" as "H".
    iVs (@own_update with "[H]") as "Y"; eauto.
    - eapply new_marked_update.
    - by rewrite /is_marked /auth_own own_op.
  Qed.

  Lemma already_marked_op (m : markingUR) l :
    l ∈ dom (gset _) m → m ≡ m ⋅ {[l := () ]}.
  Proof.
    intros Hl i; rewrite lookup_op.
    destruct (proj1 (elem_of_dom _ _) Hl) as [[] H'].
    destruct (decide (i = l)); subst;
      by [rewrite H' lookup_singleton |
       rewrite lookup_singleton_ne //= comm None_op].
  Qed.

  Lemma already_marked {E} (m : markingUR) l :
    l ∈ dom (gset _) m → own graph_marking_name (● m) ⊢ |={E}=>
  own graph_marking_name (● m) ★ μ(l).
  Proof.
    iIntros (Hl) "Hm". iVs (new_marked with "Hm") as "[H1 H2]"; iFrame.
    by rewrite -already_marked_op.
  Qed.

  Lemma marked_auth_fragment_update (m : markingUR) :
    (● m ⋅ ◯ ∅) ~~> (● (m ⋅ m) ⋅ ◯ m).
  Proof.
    rewrite <- (ucmra_unit_left_id m) at 1.
    rewrite (cmra_comm m).
    apply auth_update, new_marked_local_update.
  Qed.

  Lemma marked_auth_fragment {E} (m : markingUR) :
    own graph_marking_name (● m)
    ={E}=> own graph_marking_name (● (m)) ★ own graph_marking_name (◯ (m)).
  Proof.
    iIntros "H1".
    iVs (auth_empty (A := markingUR) graph_marking_name) as "H2".
    unfold auth_own. iCombine "H1" "H2" as "H".
    iVs (@own_update with "[H]") as "Y"; eauto.
    - eapply marked_auth_fragment_update.
    - by rewrite own_op -dup_marking.
  Qed.

  Lemma elem_of_fragment_marked (m : markingUR) l :
    l ∈ dom (gset _) m →
    own graph_marking_name (◯ (m)) ⊢ μ(l).
  Proof.
    iIntros (Hl) "Hm". rewrite (already_marked_op m l); eauto.
    rewrite /is_marked /auth_own auth_frag_op.
      by iDestruct "Hm" as "[Hm1 Hm2]".
  Qed.

  Lemma new_marking_dom m x :
    dom (gset loc) (m ⋅ {[x := ()]}) = {[x]} ∪ dom (gset loc) m.
  Proof.
    apply mapset_eq =>i.
    rewrite elem_of_union ?elem_of_dom elem_of_singleton lookup_op.
    destruct (decide (i = x)); subst.
    - rewrite lookup_singleton.
      match goal with |- _ ↔ _ ∨ is_Some ?A => destruct A end; split; eauto.
    - rewrite lookup_singleton_ne //= cmra_comm None_op; tauto.
  Qed.

End marking_definitions.

Notation "'μ(' x )" := (is_marked x) (format "μ( x )").

Definition opl_heap (w : option loc) : val :=
  match w with
  | None => NONEV
  | Some l => SOMEV #l
  end.

Lemma to_val_opl_heap w : to_val (opl_heap w) = Some (opl_heap w).
Proof. by destruct w. Qed.

Definition pr_opl_heap (w : (option loc * option loc)) : val :=
  (opl_heap (w.1), opl_heap (w.2)).

Lemma to_val_pr_opl_heap w : to_val (pr_opl_heap w) = Some (pr_opl_heap w).
Proof. by destruct w as [[|] [|]]. Qed.

Lemma to_val_pr_opl_heap' w1 w2 :
  to_val (opl_heap w1, opl_heap w2) = Some ((opl_heap w1, opl_heap w2)%V).
Proof. by destruct w1; destruct w2. Qed.

(* convert the data of a node to a value in the heap *)
Definition ND_to_heap (v : bool * (option loc * option loc)) : val * val :=
  match v with
  | (m, w) => (#m, pr_opl_heap w)
  end.

Definition to_graph_elem (v : bool * (option loc * option loc)) :
  option (exclR chlC) :=
  match v with
  | (m, w) => if m then Excl' w else None
  end.

Definition to_graph (g : graph loc) :
  (gmapR loc (exclR chlC)) := omap to_graph_elem g.

Definition MKgraph (g : graph loc) : graphUR := Some (1%Qp, to_graph g).

Definition of_graph_elem (γ : (gmapR loc (exclR chlC))) i v
  : option (bool * (option loc * option loc)) :=
  match γ !! i with
  | Excl' w => Some (true, w)
  | Some Excl_bot => None
  | None => Some v
  end.

Definition node_agrees (v v' : option loc * option loc) :=
  match v with
  | (None, None) => True
  | (Some x1, None) => v'.1 = Some x1
  | (None, Some x2) => v'.2 = Some x2
  | (Some _, Some _) => v = v'
  end.

Definition graph_agrees (g : graph loc) (γ : (gmapR loc (exclR chlC))) :=
  ∀ i v, γ !! i = Excl' v →
         ∃ v', g !! i = Some (false, v') ∧ node_agrees v v'.

Definition of_graph (g : graph loc) (γ : (gmapR loc (exclR chlC))) : graph loc
  := (map_imap (of_graph_elem γ) g).

Section definitions.
  Context `{heapG Σ, graphG Σ}.

  Definition own_graph (q : frac) γ : iProp Σ :=
    own graph_name (◯ (Some (q, γ) : graphUR)).

  Global Instance own_graph_proper q : Proper ((≡) ==> (⊣⊢)) (own_graph q).
  Proof. solve_proper. Qed.

  Definition graph_inv (g : graph loc) (Mrk : gmap loc loc) : iProp Σ :=
    (∃ γ μ,
        (own graph_name (● (Some (1%Qp, γ) : graphUR)))
          ★ (own graph_marking_name (● (μ : markingUR)))
          ★ ([★ map] l ↦ v ∈ (of_graph g γ),
             ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                          ★ m ↦ (ND_to_heap v).1)
          ★ ■ (dom (gset _) μ = marked (of_graph g γ))
          ★ ■ (dom (gset _) γ ⊆ dom (gset _) g)
          ★ ■ (graph_agrees g γ)
    )%I.

  Global Instance graph_inv_timeless g Mrk : TimelessP (graph_inv g Mrk).
  Proof. apply _. Qed.

  Context `{cinvG Σ}.
  Definition graph_ctx κ g Mrk : iProp Σ := cinv graphN κ (graph_inv g Mrk).

  Global Instance graph_ctx_persistent κ g Mrk : PersistentP (graph_ctx κ g Mrk).
  Proof. apply _. Qed.

End definitions.

Notation "'Γρ(' q , γ )" := (own_graph q γ) (format "'Γρ(' q ,  γ )").

Notation "'Γρ(' q , l [↦] v )" :=
  (own_graph q {[l := Excl v]}) (format "'Γρ(' q ,  l  [↦]  v )").

Typeclasses Opaque graph_ctx graph_inv own_graph.
(*Instance: Params (@graph_inv) 1.
Instance: Params (@own_graph) 5.
Instance: Params (@graph_ctx) 4.*)


Lemma MKgraph_valid g : ✓ MKgraph g.
Proof.
  split. done.
  intros l. rewrite lookup_omap. unfold graph in *. case (g !! l); simpl.
  - by intros [[] w].
  - done.
Qed.

Lemma from_to_graph g : marked g = ∅ → of_graph g (to_graph g) = g.
Proof.
  intros Hgm. eapply @map_eq; [typeclasses eauto|] => i.
  set (Hgm' := proj1 (mapset_eq _ _) Hgm); clearbody Hgm'; clear Hgm.
  specialize (Hgm' i). revert Hgm'.
  rewrite /of_graph /of_graph_elem /to_graph /to_graph_elem /marked
          elem_of_empty elem_of_mapset_dom_with lookup_imap lookup_omap.
  match goal with
    |- (∃ x, ?A = _ ∧ _) ↔ False → ?A ≫= (λ v, match ?A ≫= _ with _ => _ end) = ?A =>
      by destruct A as [[[] ?]|]; simpl
  end.
Qed.


Lemma to_unmarked_graph g : marked g = ∅ → to_graph g = ∅.
Proof.
  intros H1; eapply @map_eq; [typeclasses eauto|] => i.
  set (H1' := proj1 (mapset_eq _ _) H1 i); clearbody H1' ; clear H1;
    revert H1'.
  unfold graph in *.
  rewrite /marked elem_of_mapset_dom_with elem_of_empty /to_graph lookup_omap
          lookup_empty /to_graph_elem.
  destruct (g !! i) as [[[] ?]|]; simpl; trivial.
  intros [H1 _]; exfalso; apply H1; eauto.
Qed.

Lemma to_graph_agrees g : marked g = ∅ → graph_agrees g (to_graph g).
Proof. intros i v H1. rewrite to_unmarked_graph //=. Qed.

Section graph_ctx_alloc.
  Context `{heapG Σ, cinvG Σ, authG Σ markingUR, authG Σ graphUR}.

  Lemma graph_ctx_alloc (E : coPset) (g : graph loc) (Mrk : gmap loc loc)
        (Hme : marked g = ∅)
        (HNE : (nclose graphN) ⊆ E)
    :
      ([★ map] l ↦ v ∈ g,
       ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                    ★ m ↦ (ND_to_heap v).1)
      ={E}=>
  ∃ (Ig : graphG Σ) (κ : gname),
    cinv_own κ 1 ★ graph_ctx κ g Mrk ★ Γρ(1%Qp, ∅).
  Proof.
    iIntros "H1".
    iVs (own_alloc (● (∅ : markingUR))) as (mn) "H2"; first done.
    iVs (own_alloc (● (MKgraph g) ⋅ ◯ (MKgraph g))) as (gn) "H3".
    { split; auto using MKgraph_valid. }
    iDestruct "H3" as "[H31 H32]".
    set (Ig := GraphG _ _ mn _ gn).
    iExists Ig.
    iAssert (graph_inv g Mrk) with "[H1 H2 H31]" as "H".
    { unfold graph_inv. iExists (to_graph g), ∅.
      iFrame "H2 H31".
      iSplitL. by rewrite from_to_graph.
      repeat iSplit; iPureIntro.
      - by rewrite from_to_graph ?dom_empty_L.
      - rewrite to_unmarked_graph //= dom_empty.
      - by apply to_graph_agrees. }
    iVs (cinv_alloc _ graphN with "[H]") as (κ) "[Hinv key]".
    { iNext. iExact "H". }
    iExists κ.
    rewrite /own_graph /graph_ctx /MKgraph to_unmarked_graph //=; by iFrame.
  Qed.

End graph_ctx_alloc.

Lemma marked_was_unmarked (γ : gmapR loc (exclR chlC)) x v :
  ✓ ({[x := Excl v]} ⋅ γ) → γ !! x = None.
Proof.
  intros H2; specialize (H2 x).
  revert H2; rewrite lookup_op lookup_singleton. intros H2.
    by rewrite (excl_validN_inv_l O _ _ (proj1 (cmra_valid_validN _) H2 O)).
Qed.

Lemma mark_update_lookup_base (γ : gmapR loc (exclR chlC)) x v :
  ✓ ({[x := Excl v]} ⋅ γ) → ({[x := Excl v]} ⋅ γ) !! x = Some (Excl v).
Proof.
  intros H2; rewrite lookup_op lookup_singleton.
  erewrite marked_was_unmarked; eauto.
Qed.

Lemma mark_update_lookup_ne_base (γ : gmapR loc (exclR chlC)) x i v :
  i ≠ x → ({[x := Excl v]} ⋅ γ) !! i = γ !! i.
Proof. intros H. by rewrite lookup_op lookup_singleton_ne //= None_op. Qed.

Lemma nodes_agree_refl v : node_agrees v v.
Proof. by destruct v as [[|] [|]]; simpl. Qed.

Lemma agrees_deleted g γ x :
  (graph_agrees g γ) → (graph_agrees g (delete x γ)).
Proof.
  intros H1 i v H2. destruct (decide (i = x)); subst.
  - rewrite lookup_delete in H2; congruence.
  - rewrite lookup_delete_ne //= in H2; auto.
Qed.

Lemma agrees_op g γ x v :
  ✓ ({[x := Excl v]} ⋅ γ) →
  (graph_agrees g ({[x := Excl v]} ⋅ γ))
    ↔ graph_agrees g γ ∧ (∃ v', g !! x = Some (false, v') ∧ node_agrees v v').
Proof.
  intros H1; split; intros H2; unfold graph_agrees in *.
  - refine ((λ H, conj (λ i, (proj1 (H i)))
                       ((λ i (Heq : i = x),
                         proj2 (H i) Heq) x (Logic.eq_refl))) _).
    intros i. destruct (decide (i = x)); subst; split.
    + intros w H3; erewrite marked_was_unmarked in H3; eauto; congruence.
    + specialize (H2 x v); rewrite mark_update_lookup_base //= in H2; eauto.
    + intros w H3; specialize (H2 i w);
        rewrite mark_update_lookup_ne_base //= in H2; eauto.
    + tauto.
  - intros i w H3; destruct (decide (i = x)); subst; destruct H2 as [H21 H22].
    + rewrite mark_update_lookup_base //= in H3; inversion H3; subst; eauto.
    + rewrite mark_update_lookup_ne_base //= in H3; eauto.
Qed.

Lemma of_graph_dom g γ :
  ✓ γ →
  dom (gset _) (of_graph g γ) = dom (gset _) g.
Proof.
  intros H1.
  apply mapset_eq=>i. specialize (H1 i).
  rewrite ?elem_of_dom /is_Some /of_graph /of_graph_elem lookup_imap.
  unfold graph, loc in *.
  destruct (g !! i) as [x|]; simpl; trivial. revert H1.
  match goal with
    |- ✓ ?A
      → (∃ x, match ?A1 with | _ => _ end = _) ↔ _ =>
    change A1 with A; destruct A as [[]|]; inversion 1; trivial; split; eauto
  end.
Qed.

Lemma of_graph_marked_disjoint g γ γ':
  marked g = ∅ → ✓ (γ ⋅ γ') → marked (of_graph g γ) ⊥ marked (of_graph g γ').
Proof.
  rewrite elem_of_disjoint.
  intros Hgnm H1 x; specialize (H1 x).
  pose proof (proj1 (mapset_eq _ _) Hgnm x) as Hgnm'.
  clear Hgnm; revert Hgnm' H1.
  rewrite lookup_op /marked ?elem_of_mapset_dom_with /of_graph /of_graph_elem
          ?lookup_imap elem_of_empty.
  match goal with
    |- (∃ x, ?C = _ ∧ _) ↔ False → ✓ (?A ⋅ ?B)
      → (∃ x, ?C ≫= (λ v, match ?A1 with _ => _ end) = _ ∧ _)
      → (∃ x, ?C ≫= (λ v, match ?B1 with _ => _ end) = _ ∧ _) → False
    => change A1 with A; change B1 with B; destruct A as [[]|];
        destruct B as [[]|]; destruct C; simpl; inversion 1; eauto
  end.
Qed.

Lemma of_graph_unmarked_orig g γ :
  ∀ (x : loc) (l r : option loc),
    of_graph g γ !! x = Some (false, (l, r)) → g !! x = Some (false, (l, r)).
Proof.
  intros x l r.
  rewrite /of_graph ?lookup_imap /of_graph_elem.
  by case _ : (g !! x); case _ : (γ !! x) => [[]|]; inversion 1.
Qed.

Lemma of_graph_agree_unmarked g γ γ' :
  ∀ (x : loc) (l1 l2 r1 r2 : option loc),
    of_graph g γ !! x = Some (false, (l1, r1))
    → of_graph g γ' !! x = Some (false, (l2, r2)) → l1 = l2 ∧ r1 = r2.
Proof.
  intros x l1 l2 r1 r2.
  rewrite /of_graph ?lookup_imap /of_graph_elem.
  match goal with
    |- ?A ≫= (λ v, match ?B with _ => _ end) = _
      → ?A ≫= (λ v, match ?C with _ => _ end) = _ → _ =>
    destruct A; destruct B as [[]|]; destruct C as [[]|]; simpl;
      by inversion 1; inversion 1
  end.
Qed.

Lemma of_graph_op_singleton_unmarked g u1 u2 l γ :
  l ∈ dom (gset _) g →
  ✓ ({[l := Excl (u1, u2)]} ⋅ γ) → of_graph g γ !! l = g !! l.
Proof.
  intros H1 H2; specialize (H2 l); revert H1 H2.
  rewrite elem_of_dom /is_Some lookup_op /of_graph /of_graph_elem
          lookup_imap lookup_singleton.
  match goal with
    |- (∃ x, ?B = _) → ✓ (_ ⋅ ?A) →
      ?B1 ≫= (λ v, match ?A1 with _ => _ end) = ?B2 =>
    change B2 with B; change B1 with B; change A1 with A; destruct B;
      destruct A as [[]|]; intros [v Hv]; by inversion Hv; inversion 1; subst
  end.
Qed.

Lemma of_graph_op_combine g γ γ' :
  marked g = ∅ → ✓ (γ ⋅ γ') →
  of_graph g (γ ⋅ γ') = combine_graphs (of_graph g γ) (of_graph g γ').
Proof.
  intros Hgm H1. eapply @map_eq; [typeclasses eauto|] => i.
  set (Hgm' := proj1 (mapset_eq _ _) Hgm); clearbody Hgm'; clear Hgm.
  specialize (H1 i); specialize (Hgm' i). revert Hgm' H1.
  rewrite /combine_graphs.
  erewrite lookup_merge; [| apply combine_node_data_DiagNone].
  rewrite ?elem_of_dom /is_Some /of_graph /of_graph_elem
          ?lookup_imap lookup_op /marked  elem_of_mapset_dom_with
          elem_of_empty. unfold graph, loc in *.
  destruct (g !! i) as [[[] [v1 v2]]|]; simpl; trivial;
    [intros [H1 _]; exfalso; apply H1; eauto| intros _].
  match goal with
    |- ✓ (?A ⋅ ?B) →
      match ?A ⋅ ?B with _ => _ end =
      _ match ?A1 with _ => _ end match ?B1 with _ => _ end =>
    change A1 with A; change B1 with B;
      destruct A as [[[? ?]|]|]; destruct B as [[[? ?]|]|];
        inversion 1; simpl; trivial
  end.
  unfold bool_decide; repeat destruct option_eq_dec; simpl; congruence.
Qed.

Lemma of_graph_singleton_op g l u1 u2 γ :
  l ∈ dom (gset _) g →
  marked g = ∅ → ✓ ({[l := Excl (u1, u2)]} ⋅ γ) →
  of_graph g ({[l := Excl (u1, u2)]} ⋅ γ) =
  <[l := (true, (u1, u2))]>(of_graph g γ).
Proof.
  rewrite elem_of_dom. intros [v Hv] Hgm H1.
  eapply @map_eq; [typeclasses eauto|]. intros i. specialize (H1 i).
  revert H1.
  destruct (decide (i = l)); subst.
  - rewrite /of_graph /of_graph_elem lookup_insert ?lookup_imap ?Hv //=
            lookup_op lookup_insert.
    match goal with
      |- ✓ (_ ⋅ ?A) → match _ ⋅ ?A with _ => _ end = _ =>
      destruct A as [[|]|]; simpl; inversion 1; trivial
    end.
  - rewrite /of_graph /of_graph_elem lookup_insert_ne //= ?lookup_imap ?Hv //=
            lookup_op lookup_insert_ne //= lookup_empty.
    unfold graph in *; destruct (g !! i); trivial; simpl.
    match goal with
      |- ✓ (_ ⋅ ?A) → match _ ⋅ ?A with _ => _ end = match ?A1 with _ => _ end =>
      change A1 with A; destruct A as [[|]|]; simpl; inversion 1; trivial
    end.
Qed.

(** Conversion to heaps and back *)
Global Instance of_graph_proper g : Proper ((≡) ==> (=)) (of_graph g).
Proof. solve_proper. Qed.

Definition graph_mon_to_ND u w : to_graph_elem u = Excl' w → u = (true, w).
Proof. by destruct u as [[] ?]; simpl; inversion 1. Qed.

Lemma mark_update_lookup g γ x v :
  x ∈ dom (gset _) g →
  ✓ ({[x := Excl v]} ⋅ γ) →
  of_graph g ({[x := Excl v]} ⋅ γ) !! x = Some (true, v).
Proof.
  rewrite elem_of_dom /is_Some. intros [w H1] H2.
  rewrite /of_graph /of_graph_elem lookup_imap H1; simpl.
  rewrite mark_update_lookup_base; trivial.
Qed.

Lemma mark_update_lookup_ne g γ x i v :
  i ≠ x → of_graph g ({[x := Excl v]} ⋅ γ) !! i =
          (of_graph g γ) !! i.
Proof.
  intros H. rewrite /of_graph /of_graph_elem ?lookup_imap; simpl.
  rewrite mark_update_lookup_ne_base //=.
Qed.

Lemma marking_union g x v γ :
  x ∈ dom (gset _) g →
  ✓ ({[x := Excl v]} ⋅ γ) →
  marked (of_graph g ({[x := Excl v]} ⋅ γ)) = {[x]} ∪ marked (of_graph g γ).
Proof.
  intros H1 H2; apply mapset_eq => i.
  rewrite /marked elem_of_union elem_of_singleton ?elem_of_mapset_dom_with.
  destruct (decide (i = x)); subst.
  - rewrite mark_update_lookup //=; split; eauto.
  - rewrite mark_update_lookup_ne //=; tauto.
Qed.

Lemma unmarked_from_g g γ x v:
  ✓ γ → of_graph g γ !! x = Some (false, v) → g !! x = Some (false, v).
Proof.
  intros H1; specialize (H1 x); revert H1.
  rewrite /of_graph /of_graph_elem lookup_imap.
  match goal with
    |- ✓ ?B → ?A ≫= (λ v, match ?B1 with _ => _ end) = _ → ?A1 = _ =>
    change B1 with B; change A1 with A; destruct B as [[]|];
      destruct A as [[]|]; simpl; trivial; inversion 1; congruence
  end.
Qed.

Lemma delete_marked g γ x v:
  delete x (of_graph g γ) = delete x (of_graph g ({[x := Excl v]} ⋅ γ)).
Proof.
  eapply @map_eq; [typeclasses eauto|] => i.
  destruct (decide (i = x)); subst;
    [by rewrite ?lookup_delete|
     rewrite ?lookup_delete_ne //= /of_graph /of_graph_elem ?lookup_imap].
  unfold graph in *; destruct (g !! i); simpl; trivial.
  match goal with
    |- _ = match (?A ⋅ ?B) !! _ with _ => _ end =>
      by rewrite (lookup_op A B) lookup_singleton_ne //= None_op
  end.
Qed.

Lemma mark_dom_union (γ : gmapR loc (exclR chlC)) x v :
  dom (gset _) ({[x := Excl v]} ⋅ γ) = {[x]} ∪ dom (gset _) γ.
Proof.
  apply mapset_eq => i.
  rewrite elem_of_dom lookup_op elem_of_union elem_of_singleton elem_of_dom.
  match goal with
    |- is_Some (_ ⋅ ?A) ↔ _ ∨ is_Some (?A) =>
    destruct A
  end;
    (destruct (decide (i = x)); subst;
     [rewrite lookup_singleton| rewrite lookup_singleton_ne //=]);
    split; try tauto; eauto.
Qed.

Lemma graph_equiv_eq (γ γ' : gmapR loc (exclR chlC)) :
  γ ≡ γ' → γ = γ'.
Proof. intros. fold_leibniz. done. Qed.

Lemma graph_dist_equiv (γ γ' : (gmapR loc (exclR chlC))) n
  : γ ≡{n}≡ γ' → γ ≡ γ'.
Proof. by rewrite -timeless_iff. Qed.

Lemma unmarked_in_graph_mon g γ x v:
  of_graph g γ !! x = Some (false, v) → γ !! x = None.
Proof.
  rewrite /of_graph /of_graph_elem lookup_imap.
  case _ : (γ !! x) => [[]|]; case _ : (g !! x); done.
Qed.

Section graph.
  Context `{Ih : heapG Σ, Ig : graphG Σ}.

  Lemma whole_frac γ γ':
    own graph_name (● (Some (1%Qp, γ) : graphUR)) ★ Γρ(1%Qp, γ')
        ⊢
        own graph_name (● (Some (1%Qp, γ) : graphUR)) ★ Γρ(1%Qp, γ') ★ γ = γ'.
  Proof.
    iIntros "[H1 H2]". rewrite /own_graph.
    rewrite assoc -own_op. iCombine "H1" "H2" as "H".
    iDestruct (own_valid with "#H") as %[H1 H2]; cbn in *.
    iFrame "H"; iPureIntro. apply graph_equiv_eq, equiv_dist => n.
    destruct (H1 n) as [[[q u]|] H1'].
    - revert H1'; rewrite -Some_op pair_op => H1'.
      edestruct (λ H, dist_Some_inv_l _ _ _ H H1') as [z [H31 [H41 H42]]];
        try inversion H31; subst; eauto. simpl in *.
      assert (H51 : ✓ (1%Qp ⋅ q)) by (rewrite -H41; done).
      exfalso; eapply exclusive_l; eauto; try typeclasses eauto.
    - inversion H1' as [? ? H3|]; subst; inversion H3; trivial.
  Qed.

  Lemma auth_own_graph_valid q γ :
    own graph_name (● (Some (q, γ) : graphUR))
        ⊢ own graph_name (● (Some (q, γ) : graphUR)) ★ ✓ γ.
  Proof.
    iIntros "H1".
    iDestruct (own_valid with "#H1") as %[H1 [H21 H22]]; eauto.
  Qed.

  Lemma own_graph_valid q γ : Γρ(q, γ) ⊢ Γρ(q, γ) ★ ✓ γ.
  Proof.
    iIntros "H1". rewrite /own_graph.
    iDestruct (own_valid with "#H1") as %[H1 H2]; eauto.
  Qed.

  Lemma graph_divide q γ γ' :
    Γρ(q, γ ⋅ γ') ⊣⊢ Γρ(q / 2, γ) ★ Γρ(q / 2, γ').
  Proof.
    replace q with ((q / 2) + (q / 2))%Qp at 1 by (by rewrite Qp_div_2).
      by rewrite /own_graph -auth_own_op.
  Qed.

  Lemma unmarked_all_Nones g γ :
    dom (gset _) γ ⊆ dom (gset _) g →
    ✓ γ → marked (of_graph g γ) = ∅ → dom (gset _) γ = ∅.
  Proof.
    intros H1 H2 H3. apply mapset_eq =>i. specialize (H1 i). specialize (H2 i).
    set (H3' := proj1 (proj1 (mapset_eq _ _) H3 i)); clearbody H3'; clear H3.
    revert H1 H2 H3'.
    rewrite /marked /of_graph elem_of_mapset_dom_with elem_of_empty ?elem_of_dom
            /is_Some /of_graph_elem lookup_imap.
    match goal with
      |- ((∃ x, ?A = _) → ∃ x, ?B = _) →
        ✓ ?A1
        → ((∃ x, ?B1 ≫= (λ v, match ?A2 with _ => _ end) = _ ∧ _) → False)
        → (∃ x, ?A3 = Some x) ↔ False =>
      change A1 with A; change A2 with A; change A3 with A;
        destruct A as [[]|]; change B1 with B; destruct B; simpl;
          intros H1 H2 H3; split; eauto; try tauto;
            try (intros [? ?]; congruence)
    end.
    match type of H1 with
      ?A → ?B => assert (B → False); [intros [? ?]; congruence|]; eauto
    end.
  Qed.

  Lemma marking_validN {n} (γ : (gmapR loc (exclR chlC))) (q : frac) x w :
    γ !! x = None → ✓{n} Some (q, γ) → ✓{n} Some (q, {[x := Excl w]} ⋅ γ).
  Proof.
    intros H1 [H21 H22]; split; trivial; simpl in *.
    intros i; specialize (H22 i); revert H22; rewrite ?lookup_op.
    by destruct (decide (i = x)); subst;
      [rewrite ?lookup_singleton H1| rewrite ?lookup_singleton_ne ?None_op].
  Qed.

  Lemma mark_graph {E} γ q x w :
    γ !! x = None →
    (((own graph_name (● (Some (1%Qp, γ) : graphUR))) ★ Γρ(q, ∅))
       ⊢ |={E}=>
     ((own graph_name (● (Some (1%Qp, {[x := Excl w]} ⋅ γ) : graphUR)))
        ★ Γρ(q, x [↦] w))).
  Proof.
    intros Hx.
    iIntros "[H1 H2]". iCombine "H1" "H2" as "H".
    rewrite ?own_graph_eq /own_graph -?own_op -?auth_both_op.
    iVs (own_update with "H") as "H'"; eauto.
    intros n [[[mza|] [[qo mzo]|]]|]; simpl;
      rewrite /validN /cmra_validN //= /auth_validN; simpl.
    - intros [[u H1] H2]; split; auto using marking_validN. revert H1.
      destruct u as [[qu u]|]; rewrite /prod_op //= ucmra_unit_left_id;
        intros H1; inversion H1 as [? ? [H11 H12] H13|]; subst; simpl in *.
      + eexists (Some (qu, u)).
        by repeat rewrite /prod_op //=; rewrite -H11 -assoc -H12.
      + eexists (None). by rewrite //= -H11 -H12.
    - intros [[u H1] H2]; split; auto using marking_validN. revert H1.
      destruct u as [[qu u]|]; repeat rewrite /prod_op //=;
                                      rewrite ?ucmra_unit_left_id;
      intros H1; inversion H1 as [? ? [H11 H12] H13|]; subst; simpl in *.
      + eexists (Some (qu, u)).
        by repeat rewrite /prod_op //=; rewrite -H11 -H12.
      + eexists (None). rewrite //= -H11.
        repeat constructor; simpl. by rewrite H12 ?ucmra_unit_right_id.
    - intros [[u H1] H2]; split; auto using marking_validN. revert H1.
      destruct u as [[qu u]|]; repeat rewrite /prod_op //=;
                                      rewrite ?ucmra_unit_left_id;
      intros H1; inversion H1 as [? ? [H11 H12] H13|]; subst; simpl in *.
      + eexists (Some (qu, u)).
        by repeat rewrite /prod_op //=; rewrite -H11 -H12.
      + eexists (None). rewrite //= -H11.
        repeat constructor; simpl. by rewrite H12 ?ucmra_unit_right_id.
  Qed.

  Lemma updating_graph_validN {n} {γ : (gmapR loc (exclR chlC))} {x m w} :
    γ !! x = None → ✓{n} ({[x := Excl m]} ⋅ γ) → ✓{n} ({[x := Excl w]} ⋅ γ).
  Proof.
    intros H1 H2.
    intros i; specialize (H2 i); revert H2; rewrite ?lookup_op.
    by destruct (decide (i = x)); subst;
      [rewrite ?lookup_singleton H1| rewrite ?lookup_singleton_ne ?None_op].
  Qed.

  Lemma updating_graph_valid {γ : (gmapR loc (exclR chlC))} {x m w} :
    γ !! x = None → ✓ ({[x := Excl m]} ⋅ γ) → ✓ ({[x := Excl w]} ⋅ γ).
  Proof.
    intros H1 H2. apply cmra_valid_validN.
    intros n; eapply updating_graph_validN; eauto.
  Qed.

  Lemma updating_validN {n} (γ : (gmapR loc (exclR chlC))) (q : frac) x m w :
    γ !! x = None → ✓{n} Some (q, {[x := Excl m]} ⋅ γ) →
    ✓{n} Some (q, {[x := Excl w]} ⋅ γ).
  Proof.
    intros H1 [H21 H22]; split; trivial; simpl in *.
    eapply updating_graph_validN; eauto.
  Qed.

  Lemma substitute_in_graph n (γ : (gmapR loc (exclR chlC))) x m w f:
    ✓{n} ({[x := Excl m]} ⋅ γ) →
    {[x := Excl m]} ⋅ γ ≡{n}≡ {[x := Excl m]} ⋅ f →
    {[x := Excl w]} ⋅ γ ≡{n}≡ {[x := Excl w]} ⋅ f.
  Proof.
    intros H1 H2 i. specialize (H1 i); specialize (H2 i).
    match type of H2 with
      _ ≡{_}≡ ?A => assert (H3 : ✓{n} A); [by rewrite -H2|]
    end. revert H1 H2 H3.
    destruct (decide (i = x)); subst; rewrite ?lookup_op;
      [rewrite ?lookup_singleton| rewrite ?lookup_singleton_ne //=].
    intros H1 H2 H3.
    match goal with
      |- _ ⋅ ?A ≡{n}≡ _ ⋅ ?B =>
      by destruct A as [[]|]; destruct B as [[]|]; inversion H1; inversion H3
    end.
  Qed.

  Lemma substitute_in_graph_no_frame n (γ : (gmapR loc (exclR chlC))) x m w:
    ✓{n} ({[x := Excl m]} ⋅ γ) →
    {[x := Excl m]} ⋅ γ ≡{n}≡ {[x := Excl m]} →
    {[x := Excl w]} ⋅ γ ≡{n}≡ {[x := Excl w]}.
  Proof.
    intros H1 H2 i. specialize (H1 i); specialize (H2 i). revert H1 H2.
    destruct (decide (i = x)); subst; rewrite ?lookup_op;
      [rewrite ?lookup_singleton| rewrite ?lookup_singleton_ne //=].
    intros H1 H2. match goal with
                    |- _ ⋅ ?A ≡{n}≡ _ =>
                      by destruct A as [[]|]; inversion H1
                  end.
  Qed.

  Lemma update_graph {E} γ q x w m :
    γ !! x = None →
    ((own graph_name (● (Some (1%Qp, {[x := Excl m]} ⋅ γ) : graphUR)))
       ★ Γρ(q, x [↦] m))
      ⊢ |={E}=> ((own graph_name
                     (● (Some (1%Qp, {[x := Excl w]} ⋅ γ) : graphUR)))
                  ★ Γρ(q, x [↦] w)).
  Proof.
    intros Hx.
    iIntros "[H1 H2]". iCombine "H1" "H2" as "H".
    rewrite ?own_graph_eq /own_graph -?own_op.
    iVs (own_update with "H") as "H'"; eauto.
    intros n [[[mza|] [[qo mzo]|]]|]; simpl;
      rewrite /validN /cmra_validN //= /auth_validN; simpl.
    - intros [[u H1] H2]; split; eauto using updating_validN. revert H1.
      inversion H2 as [H21 H22]; simpl in *.
      destruct u as [[qu u]|]; repeat rewrite /prod_op //=;
        intros H1; inversion H1 as [? ? [H11 H12] H13|]; subst; simpl in *.
      + eexists (Some (qu, u)).
        repeat rewrite /prod_op //=. rewrite -H11; repeat constructor; simpl.
        revert H12; rewrite -?assoc; eauto using substitute_in_graph.
      + eexists (None). rewrite //= -H11. repeat constructor; simpl.
        revert H12; rewrite -?assoc; eauto using substitute_in_graph.
    - intros [[u H1] H2]; split; eauto using updating_validN. revert H1.
      inversion H2 as [H21 H22]; simpl in *.
      destruct u as [[qu u]|]; repeat rewrite /prod_op //=;
        intros H1; inversion H1 as [? ? [H11 H12] H13|]; subst; simpl in *.
      + eexists (Some (qu, u)).
        repeat rewrite /prod_op //=. rewrite -H11; repeat constructor; simpl.
        revert H12; rewrite -?assoc; eauto using substitute_in_graph.
      + eexists (None). rewrite //= -H11. repeat constructor; simpl.
        eauto using substitute_in_graph_no_frame.
    - intros [[u H1] H2]; split; eauto using updating_validN. revert H1.
      inversion H2 as [H21 H22]; simpl in *.
      destruct u as [[qu u]|]; repeat rewrite /prod_op //=;
        intros H1; inversion H1 as [? ? [H11 H12] H13|]; subst; simpl in *.
      + eexists (Some (qu, u)).
        repeat rewrite /prod_op //=. rewrite -H11; repeat constructor; simpl.
        revert H12; rewrite -?assoc; eauto using substitute_in_graph.
      + eexists (None). rewrite //= -H11. repeat constructor; simpl.
        eauto using substitute_in_graph_no_frame.
  Qed.

  Lemma auth_subgraph_base {q q' : Qp} {γ γ' : (gmapR loc (exclR chlC))} :
    ✓ (● Some (q, γ) ⋅ ◯ Some (q', γ')) →
    ∀ i v, γ' !! i = Some v → γ !! i = Some v.
  Proof.
    intros [H1 H2]; simpl in *.
    specialize (H1 O).
    revert H1. intros [[[s u]|] H1].
    - inversion H1 as [? ? H3|]; subst; clear H1.
      destruct H3 as [_ H3]. eapply graph_dist_equiv in H3; simpl in *.
      rewrite (graph_equiv_eq _ _ H3). intros i; specialize (H3 i); revert H3.
      rewrite ?lookup_op.
      destruct H2 as [_ H2]; specialize (H2 i); simpl in H2; revert H2.
      match goal with
        |- ✓ ?A1 → ?A2 ≡ ?B1 ⋅ ?C1 → ∀ v, ?B2 = _ → ?B3 ⋅ ?C2 = _ =>
        change A2 with A1; change B3 with B1; change B2 with B1;
          change C2 with C1;
          destruct A1 as [[[]|]|]; destruct B1 as [[[]|]|];
            destruct C1 as [[[]|]|]; simpl in *;
              intros H1 H2; inversion H1;
                inversion H2 as [? ? H3|]; subst; try inversion H3;
                try congruence; eauto
      end.
    - inversion H1 as [? ? H3|]; subst; clear H1.
      destruct H3 as [_ H3]. simpl in *.
        by rewrite (graph_equiv_eq _ _ (graph_dist_equiv _ _ _ H3)).
  Qed.

  Lemma auth_subgraph (q q' : Qp) (γ γ' : (gmapR loc (exclR chlC))) :
    ✓ (● Some (q, γ) ⋅ ◯ Some (q', γ')) →
    ∀ i, i ∈ dom (gset _) γ' → i ∈ dom (gset _) γ.
  Proof.
    intros H1 i. rewrite ?elem_of_dom /is_Some. intros [u Hu].
    erewrite auth_subgraph_base; eauto.
  Qed.

  Lemma auth_of_graph_subgraph g (q q' : Qp) (γ γ' : (gmapR loc (exclR chlC))) :
    marked g = ∅ →
    ✓ (● Some (q, γ) ⋅ ◯ Some (q', γ')) →
    ∀ i v, (of_graph g γ') !! i = Some (true, v) →
           (of_graph g γ) !! i = Some (true, v).
  Proof.
    intros Hgnm Hvl i v.
    assert (Hvl2 : ✓ γ').
    { inversion Hvl as [Hvl1 [_ Hvl2]]; simpl in *. specialize (Hvl1 O).
      destruct Hvl1 as [z Hvl1].
      destruct z as [[z1 z2]|]; inversion Hvl1 as [? ? [_ Hvl1']|];
        subst; simpl in *; apply graph_dist_equiv in Hvl1'.
      - eapply cmra_valid_op_l; by erewrite <- Hvl1'.
      - by rewrite -Hvl1'. } specialize (Hvl2 i).
    pose proof (proj1 (proj1 (mapset_eq _ _) Hgnm i)) as Hgnm'; clear Hgnm.
    revert Hvl2 Hgnm'.
    rewrite /marked ?elem_of_mapset_dom_with elem_of_empty /of_graph
            ?lookup_imap /of_graph_elem.
    match goal with
      |- ✓ ?B → ((∃ x, ?A = _ ∧ _) → False)
        → ?A ≫= (λ v, match ?B1 with _ => _ end) = _
        → ?A ≫= _ = _ =>
      change B1 with B; destruct A as [[[] ?]|];
        destruct B as [[|]|] eqn:Heq; simpl; intros H1 H2 H3;
          inversion H1; subst;
            try (exfalso; apply H2; eauto; fail)
    end.
    by erewrite auth_subgraph_base; eauto.
  Qed.

  Lemma auth_of_graph_marked_subgraph g (q q' : Qp)
        (γ γ' : (gmapR loc (exclR chlC))) :
    marked g = ∅ →
    ✓ (● Some (q, γ) ⋅ ◯ Some (q', γ')) →
    marked (of_graph g γ') ⊆ marked (of_graph g γ).
  Proof.
    intros H1 H2.
    apply elem_of_subseteq => x.
    rewrite /marked ?elem_of_mapset_dom_with.
    intros [[[] z2] [Hz1 Hz2]]; apply bool_decide_spec in Hz2; inversion Hz2.
    eexists; erewrite auth_of_graph_subgraph; eauto.
  Qed.

  Lemma graph_pointsto_marked γ q x w :
    ((own graph_name (● (Some (1%Qp, γ) : graphUR)))
       ★ Γρ(q, x [↦] w))
      ⊢ ((own graph_name (● (Some (1%Qp, γ) : graphUR)))
           ★ Γρ(q, x [↦] w) ★ γ = {[x := Excl w]} ⋅ (delete x γ)).
  Proof.
    rewrite /own_graph assoc -?own_op. iIntros "H".
    iDestruct (@own_valid with "#H") as %H1; simpl in *.
    iFrame. iPureIntro. apply graph_equiv_eq =>i. rewrite lookup_op.
    pose proof (auth_subgraph_base H1 x (Excl w)) as Hsb.
    revert Hsb. rewrite lookup_singleton.
    destruct (decide (i = x)); subst;
      [rewrite lookup_singleton lookup_delete cmra_comm None_op; by destruct 1
      |by rewrite lookup_singleton_ne //= lookup_delete_ne //= None_op].
  Qed.

  Lemma graph_open g Mrk γ x :
    x ∈ dom (gset _) g →
    (own graph_name (● (Some (1%Qp, γ) : graphUR)))
      ★ ([★ map] l ↦ v ∈ (of_graph g γ),
         ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                      ★ m ↦ (ND_to_heap v).1)
      ⊢ (own graph_name (● (Some (1%Qp, γ) : graphUR)))
      ★ ([★ map] l ↦ v ∈ delete x (of_graph g γ),
         ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                      ★ m ↦ (ND_to_heap v).1)
      ★ (∃ u, (of_graph g γ !! x = Some u)
                ★ ∃ (m : loc), Mrk !! x = Some m ★ x ↦ (#m, (ND_to_heap u).2)
                                               ★ m ↦ (ND_to_heap u).1).
  Proof.
    iIntros (H1) "(Hg & Ha)".
    iDestruct (@own_valid with "#Hg") as %[_ [_ Hv]].
    assert (Hid : x ∈ dom (gset _) (of_graph g γ)) by (by rewrite of_graph_dom).
    revert Hid; rewrite elem_of_dom /is_Some. intros [y Hy].
    rewrite -{1}(insert_id _ _ _ Hy) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto].
    iDestruct "Ha" as "[H $]". iFrame "Hg". iExists _; eauto.
  Qed.

  Lemma graph_close g Mrk γ x :
    ([★ map] l ↦ v ∈ delete x (of_graph g γ),
     ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2) ★
                                  m ↦ (ND_to_heap v).1)
      ★ (∃ u, (of_graph g γ !! x = Some u)
                ★ ∃ (m : loc), Mrk !! x = Some m ★ x ↦ (#m, (ND_to_heap u).2)
                                               ★ m ↦ (ND_to_heap u).1)
      ⊢ ([★ map] l ↦ v ∈ (of_graph g γ),
         ∃ (m : loc), Mrk !! l = Some m ★ l ↦ (#m, (ND_to_heap v).2)
                                      ★ m ↦ (ND_to_heap v).1).
  Proof.
    iIntros "[Ha Hl]". iDestruct "Hl" as (u) "[Hu Hl]". iDestruct "Hu" as %Hu.
    rewrite -{2}(insert_id _ _ _ Hu) -insert_delete.
    rewrite big_sepM_insert; [|apply lookup_delete_None; auto]. by iFrame "Ha".
  Qed.

  Lemma marked_is_marked_in_auth (mr : markingUR) l :
    own graph_marking_name (● mr) ★ μ(l) ⊢ ■ (l ∈ dom (gset _) mr).
  Proof.
    iIntros "H". unfold is_marked. rewrite -own_op.
    iDestruct (own_valid with "#H") as %Hvl.
    iPureIntro. rewrite elem_of_dom.
    destruct Hvl as [Hvl _]; simpl in *.
    destruct (Hvl O) as [z Hvl']. specialize (Hvl' l).
    inversion Hvl' as [? ? ? Hvl1 Hvl2|Hvl1 Hvl2]; [rewrite -Hvl1; eauto|].
    revert Hvl2. rewrite ?lookup_op lookup_empty lookup_singleton.
    case _ : (z !! l); inversion 1.
  Qed.

(* Can't prove this in the logic, I need (∀ x, ■ P → ■ ∀ x, P)
and  ((■ P → ■ Q) → ■ (P → Q)) *)

  Lemma marked_is_marked_in_auth_sepS (mr : markingUR) m :
    own graph_marking_name (● mr) ★ ([★ set] l ∈ m, μ(l))
        ⊢ ■ (m ⊆ dom (gset _) mr).
  Proof.
  Admitted.

End graph.