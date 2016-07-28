From iris.algebra Require Import base.
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
  Local Notation glu := (@lookup _ _ Graph (@gmap_lookup _ _ _ _)).

  Inductive Path g (P : bool → bool) (x : T) : T → Type :=
  | Path_O : ∀ m l r, glu x g = Some (m, (l, r)) → P m → Path g P x x
  | Path_Sl : ∀ y z m r,
      Path g P x y → bool_decide (glu y g = Some (m, (Some z, r)))
      → P m → Path g P x z
  | Path_Sr : ∀ y z m l,
      Path g P x y → bool_decide (glu y g = Some (m, (l, Some z)))
      → P m → Path g P x z.


  (* The fragment of g satisfying P is a connected graph and x is in there. *)
  Definition connected (g : Graph) P (x : T) :=
    ∀ y, y ∈ dom (gset _) g → Path g P x y.

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

End Graphs.