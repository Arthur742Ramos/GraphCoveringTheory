import GraphCoveringTheory.SchreierCover
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.Tactic

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

noncomputable instance actionCategoryFintype (M : Type u) (A : Type u)
    [Monoid M] [MulAction M A] [Fintype A] : Fintype (ActionCategory M A) :=
  Fintype.ofEquiv A (ActionCategory.objEquiv M A)

noncomputable instance coverHomFintype (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] [Fintype α] (a b : CoverVertex α A) :
    Fintype (a ⟶ b) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun e : α => FreeGroup.of e • a.back = b.back)) (by simp)

def coverGeneratorTotalEquiv (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    Quiver.Total (CoverVertex α A) ≃ A × α where
  toFun e := ⟨e.left.back, e.hom.val⟩
  invFun e :=
    ⟨(e.1 : CoverVertex α A),
      ((FreeGroup.of e.2 • e.1 : A) : CoverVertex α A),
      ⟨e.2, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨x, y, ⟨e, h⟩⟩
    rcases x with ⟨_, x⟩
    rcases y with ⟨_, y⟩
    cases h
    rfl
  right_inv e := by
    rcases e with ⟨a, e⟩
    rfl

def freeActionGeneratorTotalEquiv (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    @Quiver.Total (CoverVertex α A)
      (freeActionGroupoidIsFree α A).quiverGenerators ≃ A × α where
  toFun e := ⟨e.left.back, e.hom.val⟩
  invFun e :=
    ⟨(e.1 : CoverVertex α A),
      ((FreeGroup.of e.2 • e.1 : A) : CoverVertex α A),
      ⟨e.2, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨x, y, ⟨e, h⟩⟩
    rcases x with ⟨_, x⟩
    rcases y with ⟨_, y⟩
    cases h
    rfl
  right_inv e := by
    rcases e with ⟨a, e⟩
    rfl

noncomputable def freeGroupoidTree (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G] (r : G) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)) :=
  @geodesicSubtree
    (Symmetrify (IsFreeGroupoid.Generators G))
    (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators G))
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)

@[reducible] noncomputable def freeGroupoidTree_arborescence (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G] (r : G) :
    Arborescence (freeGroupoidTree G r) := by
  dsimp [freeGroupoidTree]
  exact @Quiver.geodesicArborescence
    (Symmetrify (IsFreeGroupoid.Generators G)) _
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)

noncomputable def freeGroupoidGeneratorSet (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Set (Quiver.Total (IsFreeGroupoid.Generators G)) :=
  (wideSubquiverEquivSetTotal
    (wideSubquiverSymmetrify (freeGroupoidTree G r)))ᶜ

lemma freeGroupoidGeneratorSet_card (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Fintype.card (freeGroupoidGeneratorSet G r) =
      Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G) := by
  classical
  let G' := IsFreeGroupoid.Generators G
  letI : RootedConnected (show Symmetrify G' from r) :=
    @IsFreeGroupoid.generators_connected G _ _ _ r
  let T := freeGroupoidTree G r
  letI : Arborescence T := freeGroupoidTree_arborescence G r
  let S : Set (Quiver.Total G') :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  letI : Fintype S := FiniteGraphFreeGroup.setSubtypeFintype S
  letI : Fintype (Sᶜ : Set (Quiver.Total G')) :=
    FiniteGraphFreeGroup.setSubtypeFintype Sᶜ
  have hS : Fintype.card S = Fintype.card G' - 1 := by
    simpa [S, T] using (FiniteGraphFreeGroup.symmetrified_tree_set_card T)
  have hcomp : Fintype.card (Sᶜ : Set (Quiver.Total G')) =
      Fintype.card (Quiver.Total G') - Fintype.card S := by
    exact @Fintype.card_subtype_compl _ _ (fun e : Quiver.Total G' => e ∈ S)
      (FiniteGraphFreeGroup.setSubtypeFintype S)
      (FiniteGraphFreeGroup.setSubtypeFintype Sᶜ)
  have htreele : Fintype.card S ≤ Fintype.card (Quiver.Total G') :=
    Fintype.card_subtype_le _
  have htreele' : Fintype.card G' - 1 ≤ Fintype.card (Quiver.Total G') := by
    rw [← hS]
    exact htreele
  have hGpos : 1 ≤ Fintype.card G' := Fintype.card_pos_iff.mpr ⟨r⟩
  change Fintype.card (Sᶜ : Set (Quiver.Total G')) =
    Fintype.card (Quiver.Total G') + 1 - Fintype.card G'
  rw [hcomp, hS]
  omega

noncomputable def generatorComplement (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) :
    Set (Quiver.Total (IsFreeGroupoid.Generators G)) :=
  (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ

lemma generatorComplement_card (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)))
    [Arborescence T] :
    Fintype.card (generatorComplement G T) =
      Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G) := by
  classical
  let G' := IsFreeGroupoid.Generators G
  let S : Set (Quiver.Total G') :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  letI : Fintype S := FiniteGraphFreeGroup.setSubtypeFintype S
  letI : Fintype (Sᶜ : Set (Quiver.Total G')) :=
    FiniteGraphFreeGroup.setSubtypeFintype Sᶜ
  have hS : Fintype.card S = Fintype.card G' - 1 := by
    simpa [S] using (FiniteGraphFreeGroup.symmetrified_tree_set_card T)
  have hcomp : Fintype.card (Sᶜ : Set (Quiver.Total G')) =
      Fintype.card (Quiver.Total G') - Fintype.card S := by
    exact @Fintype.card_subtype_compl _ _ (fun e : Quiver.Total G' => e ∈ S)
      (FiniteGraphFreeGroup.setSubtypeFintype S)
      (FiniteGraphFreeGroup.setSubtypeFintype Sᶜ)
  have htreele : Fintype.card S ≤ Fintype.card (Quiver.Total G') :=
    Fintype.card_subtype_le _
  have htreele' : Fintype.card G' - 1 ≤ Fintype.card (Quiver.Total G') := by
    rw [← hS]
    exact htreele
  have hGpos : 1 ≤ Fintype.card G' := by
    exact Fintype.card_pos_iff.mpr ⟨show G' from root T⟩
  change Fintype.card (Sᶜ : Set (Quiver.Total G')) =
    Fintype.card (Quiver.Total G') + 1 - Fintype.card G'
  rw [hcomp, hS]
  omega

theorem freeGroupoid_end_free_rank (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Nonempty (End r ≃* FreeGroup (Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G)))) := by
  let T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)) :=
    @geodesicSubtree
      (Symmetrify (IsFreeGroupoid.Generators G))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators G))
      (show Symmetrify (IsFreeGroupoid.Generators G) from r)
      (@IsFreeGroupoid.generators_connected G _ _ _ r)
  letI : Arborescence T := @Quiver.geodesicArborescence
    (Symmetrify (IsFreeGroupoid.Generators G)) _
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)
  let X := generatorComplement G T
  letI : Fintype X :=
    FiniteGraphFreeGroup.setSubtypeFintype _
  have hroot : (show G from root T) = r := by
    rfl
  let B : FreeGroupBasis X (End r) := by
    rw [← hroot]
    simpa [X, generatorComplement] using (FiniteGraphFreeGroup.spanningTreeBasis T)
  have hcard := generatorComplement_card G T
  let eX : X ≃ Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G)) :=
    hcard ▸ Fintype.equivFin X
  exact ⟨(B.reindex eX).repr⟩

theorem schreier_index_formula_nat (n : ℕ) (H : Subgroup (FreeGroup (Fin n)))
    [H.FiniteIndex] :
    Nonempty (H ≃* FreeGroup (Fin (H.index * n + 1 - H.index))) := by
  letI : Fintype (FreeGroup (Fin n) ⧸ H) := H.fintypeQuotientOfFiniteIndex
  letI : Nonempty (FreeGroup (Fin n) ⧸ H) :=
    ⟨((1 : FreeGroup (Fin n)) : FreeGroup (Fin n) ⧸ H)⟩
  letI : MulAction.IsPretransitive (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H) :=
    MulAction.isPretransitive_quotient (FreeGroup (Fin n)) H
  letI : IsConnected
      (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)) :=
    zigzag_isConnected fun x y =>
      Relation.ReflTransGen.single <|
        Or.inl <| nonempty_subtype.mpr
          (show _ from MulAction.exists_smul_eq
            (FreeGroup (Fin n)) x.back y.back)
  letI : IsFreeGroupoid
      (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)) :=
    freeActionGroupoidIsFree (Fin n) (FreeGroup (Fin n) ⧸ H)
  letI : Fintype (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)) :=
    actionCategoryFintype (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)
  letI : Fintype
      (IsFreeGroupoid.Generators
        (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H))) :=
    Fintype.ofEquiv (FreeGroup (Fin n) ⧸ H)
      (ActionCategory.objEquiv (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H))
  letI : ∀ a b : IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)), Fintype (a ⟶ b) :=
    fun a b => coverHomFintype (Fin n) (FreeGroup (Fin n) ⧸ H) a b
  letI : Fintype (Quiver.Total (CoverVertex (Fin n) (FreeGroup (Fin n) ⧸ H))) :=
    FiniteGraphFreeGroup.baseTotalFintype
  letI : Fintype
      (@Quiver.Total (CoverVertex (Fin n) (FreeGroup (Fin n) ⧸ H))
        (freeActionGroupoidIsFree (Fin n) (FreeGroup (Fin n) ⧸ H)).quiverGenerators) :=
    Fintype.ofEquiv
      ((FreeGroup (Fin n) ⧸ H) × Fin n)
      (freeActionGeneratorTotalEquiv (Fin n) (FreeGroup (Fin n) ⧸ H)).symm
  letI : Fintype
      (Quiver.Total
        (IsFreeGroupoid.Generators
          (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)))) :=
    FiniteGraphFreeGroup.baseTotalFintype
  let r : ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H) :=
    ActionCategory.objEquiv (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)
      ((1 : FreeGroup (Fin n)) : FreeGroup (Fin n) ⧸ H)
  have hconn : IsConnected
      (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)) := inferInstance
  have h := @freeGroupoid_end_free_rank
    (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H))
    (by infer_instance)
    (freeActionGroupoidIsFree (Fin n) (FreeGroup (Fin n) ⧸ H))
    hconn
    (by infer_instance)
    (by exact fun a b => coverHomFintype (Fin n) (FreeGroup (Fin n) ⧸ H) a b)
    r
  have hvertices : Fintype.card
      (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H))) = H.index := by
    change Fintype.card (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)) = H.index
    calc
      Fintype.card (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)) =
          Fintype.card (FreeGroup (Fin n) ⧸ H) :=
        Fintype.card_congr (ActionCategory.objEquiv
          (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)).symm
      _ = Nat.card (FreeGroup (Fin n) ⧸ H) := Nat.card_eq_fintype_card.symm
      _ = H.index := (Subgroup.index_eq_card H).symm
  have hquotient : Fintype.card (FreeGroup (Fin n) ⧸ H) = H.index := by
    calc
      Fintype.card (FreeGroup (Fin n) ⧸ H) =
          Nat.card (FreeGroup (Fin n) ⧸ H) := Nat.card_eq_fintype_card.symm
      _ = H.index := (Subgroup.index_eq_card H).symm
  have hedges : Fintype.card
      (Quiver.Total
        (IsFreeGroupoid.Generators
          (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)))) =
      H.index * n := by
    have htotal : Fintype.card
        (Quiver.Total
          (IsFreeGroupoid.Generators
            (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)))) =
        Fintype.card ((FreeGroup (Fin n) ⧸ H) × Fin n) :=
      Fintype.card_congr (freeActionGeneratorTotalEquiv (Fin n)
        (FreeGroup (Fin n) ⧸ H))
    rw [htotal]
    simp only [Fintype.card_prod, Fintype.card_fin]
    simp [hquotient]
  rcases h with ⟨e⟩
  have e' : End r ≃* H := by
    simpa [r] using (ActionCategory.endMulEquivSubgroup H)
  have hdim :
      Fintype.card (Quiver.Total
          (IsFreeGroupoid.Generators
            (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H)))) + 1 -
          Fintype.card (IsFreeGroupoid.Generators
            (ActionCategory (FreeGroup (Fin n)) (FreeGroup (Fin n) ⧸ H))) =
        H.index * n + 1 - H.index := by
    rw [hedges, hvertices]
  have e0 : End r ≃* FreeGroup (Fin (H.index * n + 1 - H.index)) := by
    rw [hdim] at e
    exact e
  exact ⟨e'.symm.trans e0⟩

theorem schreier_index_formula_proved (n : ℕ)
    (H : Subgroup (FreeGroup (Fin n))) [H.FiniteIndex] (hn : 0 < n) :
    Nonempty (H ≃* FreeGroup (Fin (1 + H.index * (n - 1)))) := by
  have h := schreier_index_formula_nat n H
  have hm : H.index * (n - 1) = H.index * n - H.index := by
    rw [Nat.sub_one]
    exact Nat.mul_pred H.index n
  have hindex : H.index * n + 1 - H.index = 1 + H.index * (n - 1) := by
    calc
      H.index * n + 1 - H.index = 1 + H.index * n - H.index := by
        rw [Nat.add_comm (H.index * n) 1]
      _ = 1 + (H.index * n - H.index) :=
        Nat.add_sub_assoc (Nat.le_mul_of_pos_right H.index hn) 1
      _ = 1 + H.index * (n - 1) := by rw [← hm]
  rw [hindex] at h
  exact h

end GraphCoveringTheory
