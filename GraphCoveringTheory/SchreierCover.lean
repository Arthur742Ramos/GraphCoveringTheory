import Mathlib.CategoryTheory.Action
import Mathlib.Combinatorics.Quiver.Covering
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import FiniteGraphFreeGroup.Proof

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

/-!  The finite Schreier graph of a subgroup of a free group.  The vertices are
the cosets, and a generator-labelled edge sends a coset along the corresponding
left action. -/

abbrev CoverVertex (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :=
  ActionCategory (FreeGroup α) A

instance coverQuiver (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :
    Quiver (CoverVertex α A) where
  Hom x y := {e : α // FreeGroup.of e • x.back = y.back}

inductive Rose (α : Type u) : Type u where
  | point : Rose α

instance roseQuiver (α : Type u) : Quiver (Rose α) where
  Hom _ _ := α

def coverProjection (α : Type u) (A : Type u) [MulAction (FreeGroup α) A] :
    CoverVertex α A ⥤q Rose α where
  obj _ := Rose.point
  map e := e.val

def coverStarEquiv (α : Type u) (A : Type u) [MulAction (FreeGroup α) A]
    (x : CoverVertex α A) :
    Quiver.Star x ≃ Quiver.Star (Rose.point : Rose α) where
  toFun f := ⟨Rose.point, f.2.val⟩
  invFun e :=
    ⟨((FreeGroup.of e.2 • x.back : A) : CoverVertex α A),
      ⟨e.2, rfl⟩⟩
  left_inv := by
    rintro ⟨y, e⟩
    have hy :
        ((FreeGroup.of e.val • x.back : A) : CoverVertex α A) = y := by
      calc
        ((FreeGroup.of e.val • x.back : A) : CoverVertex α A) =
            (y.back : CoverVertex α A) :=
          congrArg (fun z : A => (z : CoverVertex α A)) e.property
        _ = y := ActionCategory.back_coe y
    apply Sigma.subtype_ext hy
    rfl
  right_inv := by
    rintro ⟨_, e⟩
    rfl

def coverCostarEquiv (α : Type u) (A : Type u) [MulAction (FreeGroup α) A]
    (x : CoverVertex α A) :
    Quiver.Costar x ≃ Quiver.Costar (Rose.point : Rose α) where
  toFun f := ⟨Rose.point, f.2.val⟩
  invFun e :=
    ⟨(((FreeGroup.of e.2)⁻¹ • x.back : A) : CoverVertex α A),
      ⟨e.2, by simp⟩⟩
  left_inv := by
    rintro ⟨y, e⟩
    have hy :
        (((FreeGroup.of e.val)⁻¹ • x.back : A) : CoverVertex α A) = y := by
      have heq : (FreeGroup.of e.val)⁻¹ • x.back = y.back :=
        inv_smul_eq_iff.mpr e.property.symm
      calc
        (((FreeGroup.of e.val)⁻¹ • x.back : A) : CoverVertex α A) =
            (y.back : CoverVertex α A) :=
          congrArg (fun z : A => (z : CoverVertex α A)) heq
        _ = y := ActionCategory.back_coe y
    apply Sigma.subtype_ext hy
    rfl
  right_inv := by
    rintro ⟨_, e⟩
    rfl

theorem coverProjection_isCovering (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    (coverProjection α A).IsCovering := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · let e := coverStarEquiv α A x
    have he : (coverProjection α A).star x =
        (e : Quiver.Star x → Quiver.Star (Rose.point : Rose α)) := by
      funext f
      rcases f with ⟨y, f⟩
      rfl
    rw [he]
    exact e.bijective
  · let e := coverCostarEquiv α A x
    have he : (coverProjection α A).costar x =
        (e : Quiver.Costar x → Quiver.Costar (Rose.point : Rose α)) := by
      funext f
      rcases f with ⟨y, f⟩
      rfl
    rw [he]
    exact e.bijective

/-! The action groupoid admits a smaller, explicit generating quiver when the
acting free group is presented as `FreeGroup α`.  Mathlib's general
Nielsen--Schreier instance uses an abstract chosen basis; this version keeps
the original generator type visible for the cardinality computation. -/

@[reducible] def freeActionGroupoidIsFree (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    IsFreeGroupoid (ActionCategory (FreeGroup α) A) where
  quiverGenerators :=
    ⟨fun a b => {e : α // FreeGroup.of e • a.back = b.back}⟩
  of := fun (e : Subtype _) => ⟨FreeGroup.of e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : α → (A → X) ⋊[mulAutArrow] FreeGroup α := fun e =>
      ⟨fun b => @f ⟨(), _⟩ ⟨(), b⟩ ⟨e, smul_inv_smul _ b⟩, FreeGroup.of e⟩
    let F' : FreeGroup α →* (A → X) ⋊[mulAutArrow] FreeGroup α :=
      FreeGroup.lift f'
    refine ⟨ActionCategory.uncurry F' ?_, ?_, ?_⟩
    · suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id _ by
        exact DFunLike.ext_iff.mp this
      apply FreeGroup.ext_hom
      intro e
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b⟩ ⟨e, h : FreeGroup.of e • a = b⟩
      change (F' (FreeGroup.of _)).left _ = _
      rw [FreeGroup.lift_apply_of]
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have hEF : ActionCategory.curry E = F' := by
        apply FreeGroup.ext_hom
        intro e
        ext b
        · simp only [ActionCategory.curry_apply_left]
          change E.map (ActionCategory.homOfPair b (FreeGroup.of e)) =
            (FreeGroup.lift f' (FreeGroup.of e)).left b
          rw [FreeGroup.lift_apply_of]
          change E.map (ActionCategory.homOfPair b (FreeGroup.of e)) =
            @f (((FreeGroup.of e)⁻¹ • b : A) : ActionCategory (FreeGroup α) A)
              (b : ActionCategory (FreeGroup α) A)
              ⟨e, smul_inv_smul (FreeGroup.of e) b⟩
          have h := hE
            (((FreeGroup.of e)⁻¹ • b : A) : ActionCategory (FreeGroup α) A)
            (b : ActionCategory (FreeGroup α) A)
            (⟨e, smul_inv_smul (FreeGroup.of e) b⟩)
          rw [← h]
          congr 1
        · rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intros
        simp only [← hEF, ActionCategory.uncurry_map, ActionCategory.curry_apply_left,
          ActionCategory.coe_back, ActionCategory.homOfPair.val]
        rfl

end GraphCoveringTheory
