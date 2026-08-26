import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace FiniteGraphFreeGroup

variable {V : Type u} [Quiver.{u} V]

def totalEquiv (T : WideSubquiver V) :
    Quiver.Total T ≃ Σ a : V, Σ b : V, {e : a ⟶ b // e ∈ T a b} where
  toFun e := ⟨e.left, e.right, ⟨e.hom.val, e.hom.property⟩⟩
  invFun e := ⟨e.1, e.2.1, ⟨e.2.2.1, e.2.2.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

@[reducible]
noncomputable def totalFintype [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) : Fintype (Quiver.Total T) := by
  classical
  exact Fintype.ofEquiv _ (totalEquiv T).symm

noncomputable instance totalFintypeInst [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) : Fintype (Quiver.Total T) := totalFintype T

noncomputable instance wideSubquiverHomFintype [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] (T : WideSubquiver V) (a b : T) :
    Fintype (@Quiver.Hom T T.quiver a b) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun e => e ∈ T a b) (by simp)

def baseTotalEquiv (V : Type u) [Quiver.{u} V] :
    Quiver.Total V ≃ Σ a : V, Σ b : V, a ⟶ b where
  toFun e := ⟨e.left, e.right, e.hom⟩
  invFun e := ⟨e.1, e.2.1, e.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

@[reducible]
noncomputable def baseTotalFintype [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] :
    Fintype (Quiver.Total V) := by
  classical
  exact Fintype.ofEquiv _ (baseTotalEquiv V).symm

noncomputable instance baseTotalFintypeInst [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] :
    Fintype (Quiver.Total V) := baseTotalFintype

noncomputable instance setSubtypeFintype {α : Type u} [Fintype α] (s : Set α) : Fintype s := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun x => x ∈ s) (by simp)

def wideTotalEquiv {V : Type u} [Quiver.{u} V] (H : WideSubquiver V) :
    Quiver.Total H ≃ (wideSubquiverEquivSetTotal H : Set (Quiver.Total V)) where
  toFun e := ⟨⟨e.left, e.right, e.hom.val⟩, e.hom.property⟩
  invFun e := ⟨e.1.left, e.1.right, ⟨e.1.hom, e.2⟩⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

lemma exists_last_data (T : WideSubquiver V) [Arborescence T]
    {b : T} (hb : b ≠ root T) :
    Nonempty (Σ a : T, Path (root T) a × (a ⟶ b)) := by
  let q : Path (root T) b := default
  cases q with
  | nil => exact False.elim (hb rfl)
  | cons p e => exact ⟨⟨_, p, e⟩⟩

noncomputable def lastData (T : WideSubquiver V) [Arborescence T]
    (b : {b : T // b ≠ root T}) :
    Σ a : T, Path (root T) a × (a ⟶ b.1) :=
  Classical.choice (exists_last_data T (b := b.1) b.2)

lemma default_path_length_root (T : WideSubquiver V) [Arborescence T]
    (b : T) (h : b = root T) : (default : Path (root T) b).length = 0 := by
  cases h
  exact congrArg Path.length (Subsingleton.elim _ Path.nil)

lemma target_ne_root (T : WideSubquiver V) [Arborescence T]
    (e : Quiver.Total T) : e.right ≠ root T := by
  intro h
  let p : Path (root T) e.left := default
  have hp : (default : Path (root T) e.right) = p.cons e.hom := Subsingleton.elim _ _
  have hlen := congrArg Path.length hp
  have hzero := default_path_length_root T e.right h
  simp [p, hzero] at hlen

noncomputable def treeEdgeEquiv (T : WideSubquiver V) [Arborescence T] :
    Quiver.Total T ≃ {b : T // b ≠ root T} where
  toFun e := ⟨e.right, target_ne_root T e⟩
  invFun b :=
    let d := lastData T b
    ⟨d.1, b.1, d.2.2⟩
  left_inv e := by
    let b : {b : T // b ≠ root T} := ⟨e.right, target_ne_root T e⟩
    let d := lastData T b
    have hp : d.2.1.cons d.2.2 = (default : Path (root T) e.left).cons e.hom :=
      Subsingleton.elim _ _
    have hc := Path.cons.inj hp
    rcases hc with ⟨hab, hpath, hedge⟩
    exact Quiver.Total.ext hab rfl hedge
  right_inv b := by
    rfl

lemma arborescence_card [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver V) [Arborescence T] :
    Fintype.card (Quiver.Total T) = Fintype.card V - 1 := by
  classical
  letI : Fintype T := Fintype.ofEquiv V (Equiv.refl _)
  letI : Fintype {b : T // b ≠ root T} :=
    Fintype.subtype (Finset.univ.filter fun b => b ≠ root T) (by simp)
  rw [Fintype.card_congr (treeEdgeEquiv T)]
  rw [Fintype.card_subtype_compl]
  have hcard : Fintype.card T = Fintype.card V :=
    Fintype.card_congr (Equiv.refl V)
  rw [hcard]
  simp

lemma no_reverse_edges (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    {a b : V} (e : @Quiver.Hom V _ a b)
    (h₁ : T a b (Sum.inl e)) (h₂ : T b a (Sum.inr e)) : False := by
  let p : Path (root T) a := default
  let q : Path (root T) b := default
  let f : @Quiver.Hom T T.quiver a b := ⟨Sum.inl e, h₁⟩
  let g : @Quiver.Hom T T.quiver b a := ⟨Sum.inr e, h₂⟩
  have hpq : q = p.cons f := Subsingleton.elim _ _
  have hqp : p = q.cons g := Subsingleton.elim _ _
  have hpq_len := congrArg Path.length hpq
  have hqp_len := congrArg Path.length hqp
  simp [p, q, f, g] at hpq_len hqp_len
  omega

def symEdgeForget (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total T) : Quiver.Total (wideSubquiverSymmetrify T) := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  cases f with
  | inl f => exact ⟨a, b, ⟨f, Or.inl hf⟩⟩
  | inr f => exact ⟨b, a, ⟨f, Or.inr hf⟩⟩

def symEdgeForgetInv (T : WideSubquiver (Symmetrify V))
    (e : Quiver.Total (wideSubquiverSymmetrify T)) : Quiver.Total T := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  change T a b (Sum.inl f) ∨ T b a (Sum.inr f) at hf
  by_cases h : T a b (Sum.inl f)
  · exact ⟨a, b, ⟨Sum.inl f, h⟩⟩
  · exact ⟨b, a, ⟨Sum.inr f, hf.resolve_left h⟩⟩

lemma symEdgeForgetInv_forget (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    (e : Quiver.Total T) : symEdgeForgetInv T (symEdgeForget T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  cases f with
  | inl f =>
      simp [symEdgeForget, symEdgeForgetInv]
      split
      · rfl
      · exact False.elim (‹¬T a b (Sum.inl f)› hf)
  | inr f =>
      have hn : ¬T b a (Sum.inl f) := fun h => no_reverse_edges T f h hf
      simp [symEdgeForget, symEdgeForgetInv]
      split
      · exact False.elim (hn ‹T b a (Sum.inl f)›)
      · rfl

lemma symEdgeForget_forgetInv (T : WideSubquiver (Symmetrify V)) [Arborescence T]
    (e : Quiver.Total (wideSubquiverSymmetrify T)) :
    symEdgeForget T (symEdgeForgetInv T e) = e := by
  rcases e with ⟨a, b, ⟨f, hf⟩⟩
  change T a b (Sum.inl f) ∨ T b a (Sum.inr f) at hf
  by_cases h : T a b (Sum.inl f)
  · have hinv : symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
        ⟨a, b, ⟨Sum.inl f, h⟩⟩ := by
      simp [symEdgeForgetInv, h]
    rw [hinv]
    simp [symEdgeForget]
  · have h' := hf.resolve_left h
    have hinv : symEdgeForgetInv T ⟨a, b, ⟨f, hf⟩⟩ =
        ⟨b, a, ⟨Sum.inr f, h'⟩⟩ := by
      simp [symEdgeForgetInv, h]
    rw [hinv]
    simp [symEdgeForget]

def symEdgeEquiv (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Quiver.Total T ≃ Quiver.Total (wideSubquiverSymmetrify T) where
  toFun := symEdgeForget T
  invFun := symEdgeForgetInv T
  left_inv := symEdgeForgetInv_forget T
  right_inv := symEdgeForget_forgetInv T

lemma symmetrified_tree_card [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Fintype.card (Quiver.Total (wideSubquiverSymmetrify T)) = Fintype.card V - 1 := by
  classical
  letI : Fintype (Symmetrify V) := Fintype.ofEquiv V (Equiv.refl _)
  letI : ∀ a b : Symmetrify V,
      Fintype (@Quiver.Hom (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :=
    fun a b => by
      change Fintype ((@Quiver.Hom V _ a b) ⊕ (@Quiver.Hom V _ b a))
      infer_instance
  rw [← Fintype.card_congr (symEdgeEquiv T)]
  have hcard : Fintype.card (Symmetrify V) = Fintype.card V :=
    Fintype.card_congr (Equiv.refl V)
  simpa [hcard] using (arborescence_card T)

lemma symmetrified_tree_set_card [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Fintype.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T) :
      Set (Quiver.Total V)) = Fintype.card V - 1 := by
  rw [← Fintype.card_congr (wideTotalEquiv (wideSubquiverSymmetrify T))]
  exact symmetrified_tree_card T

noncomputable def spanningTreeBasis {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set _)
      (End (show G from root T)) := by
  classical
  let X : Set _ := (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ
  apply FreeGroupBasis.ofUniqueLift X
    (fun e => IsFreeGroupoid.SpanningTree.loopOfHom T (IsFreeGroupoid.of e.val.hom))
  intro Y _ f
  let f' : Labelling (IsFreeGroupoid.Generators G) Y := fun a b e =>
    if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  rcases IsFreeGroupoid.unique_lift f' with ⟨F', hF', uF'⟩
  refine ⟨F'.mapEnd _, ?_, ?_⟩
  · suffices ∀ {x y} (q : x ⟶ y),
        F'.map (IsFreeGroupoid.SpanningTree.loopOfHom T q) = (F'.map q : Y) by
      rintro ⟨⟨a, b, e⟩, h⟩
      simp only [Functor.mapEnd, DFunLike.coe, this, hF']
      exact dif_neg h
    intro x y q
    suffices ∀ {a} (p : Path (root T) a), F'.map (IsFreeGroupoid.SpanningTree.homOfPath T p) = 1 by
      simp only [this, IsFreeGroupoid.SpanningTree.treeHom, comp_as_mul, inv_as_inv,
        IsFreeGroupoid.SpanningTree.loopOfHom, inv_one, mul_one, one_mul, Functor.map_inv,
        Functor.map_comp]
    intro a p
    induction p with
    | nil =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath]
        simpa only [id_as_one] using! F'.map_id _
    | cons p e ih =>
        rw [IsFreeGroupoid.SpanningTree.homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          exact dif_pos (Or.inl eT)
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          exact dif_pos (Or.inr eT)
  · intro E hE
    ext x
    suffices (IsFreeGroupoid.SpanningTree.functorOfMonoidHom T E).map x = F'.map x by
      simpa only [IsFreeGroupoid.SpanningTree.loopOfHom,
        IsFreeGroupoid.SpanningTree.functorOfMonoidHom, IsIso.inv_id,
        IsFreeGroupoid.SpanningTree.treeHom_root, Category.id_comp, Category.comp_id] using! this
    congr
    apply uF'
    intro a b e
    change E (IsFreeGroupoid.SpanningTree.loopOfHom T _) = dite _ _ _
    split_ifs with h
    · rw [IsFreeGroupoid.SpanningTree.loopOfHom_eq_id T e h, ← CategoryTheory.End.one_def,
        E.map_one]
    · exact hE ⟨⟨a, b, e⟩, h⟩

instance freeGroupoidIsFree : IsFreeGroupoid (Quiver.FreeGroupoid V) where
  quiverGenerators :=
    ⟨fun a b => @Quiver.Hom V _ a.as b.as⟩
  of := fun {a b} e =>
    Quiver.FreeGroupoid.of V |>.map (show @Quiver.Hom V _ a.as b.as from e)
  unique_lift := by
    intro X _ f
    let f' : Labelling V X := fun {_ _} e =>
      f (a := (Quiver.FreeGroupoid.of V).obj _) (b := (Quiver.FreeGroupoid.of V).obj _) e
    let φ : V ⥤q CategoryTheory.SingleObj X :=
      { obj := fun _ => ()
        map := fun {_ _} e => f' e }
    refine ⟨Quiver.FreeGroupoid.lift φ, ?_, ?_⟩
    · intro a b e
      cases a
      cases b
      have h := Quiver.FreeGroupoid.lift_spec φ
      have hm := congrArg (fun ψ : V ⥤q CategoryTheory.SingleObj X => ψ.map e) h
      simpa [φ, f'] using! hm
    · intro F hF
      apply Quiver.FreeGroupoid.lift_unique φ F
      apply Prefunctor.ext
      · intro a b e
        exact hF ((Quiver.FreeGroupoid.of V).obj a) ((Quiver.FreeGroupoid.of V).obj b) e
      · intro a
        rfl

class FiniteQuiver (V : Type u) [Quiver.{u} V] where
  finite_hom : ∀ a b : V, Fintype (@Quiver.Hom V _ a b)

@[reducible]
instance finiteHom {V : Type u} [Quiver.{u} V] [FiniteQuiver V] (a b : V) :
    Fintype (@Quiver.Hom V _ a b) :=
  FiniteQuiver.finite_hom (V := V) a b

class WeaklyConnected (V : Type u) [Quiver.{u} V] : Prop where
  path : ∀ a b : V,
    Nonempty (@Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b)

instance rootedConnectedFree {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root : V) :
    @RootedConnected (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      ((Quiver.FreeGroupoid.of V).obj root) where
  nonempty_path b := by
    rcases b with ⟨b⟩
    obtain ⟨p⟩ := WeaklyConnected.path root b
    induction p with
    | nil => exact ⟨Path.nil⟩
    | cons p e ih =>
        rcases e with e | e
        · exact ⟨ih.some.cons (show
              @Quiver.Hom (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                {as := _} {as := _} from Sum.inl e)⟩
        · exact ⟨ih.some.cons (show
              @Quiver.Hom (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
                {as := _} {as := _} from Sum.inr e)⟩

def generatorObjEquiv {V : Type u} [Quiver.{u} V] :
    IsFreeGroupoid.Generators (Quiver.FreeGroupoid V) ≃ V where
  toFun a := a.as
  invFun v := (Quiver.FreeGroupoid.of V).obj v
  left_inv a := by cases a; rfl
  right_inv v := rfl

noncomputable instance freeGroupoidObjFintype {V : Type u} [Quiver.{u} V]
    [Fintype V] : Fintype (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) :=
  Fintype.ofEquiv V (generatorObjEquiv).symm

noncomputable instance freeGroupoidGeneratorHomFintype {V : Type u}
    [Quiver.{u} V] [FiniteQuiver V]
    (a b : IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) :
    Fintype (a ⟶ b) := by
  change Fintype (@Quiver.Hom V _ a.as b.as)
  exact FiniteQuiver.finite_hom (V := V) a.as b.as

def vertexCount {V : Type u} [Fintype V] : ℕ := Fintype.card V

def edgeCount {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V] : ℕ :=
  Fintype.card (Quiver.Total V)

/-! The rank is written this way because subtraction in `ℕ` is truncated.  The
    spanning-tree inequality proved below shows that this is the usual first
    Betti number `E - (V - 1)` under `WeaklyConnected`. -/
abbrev cycleRank {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V] : ℕ :=
  edgeCount (V := V) + 1 - vertexCount (V := V)

/-- The endomorphism group at a root in the free groupoid generated by the graph. -/
abbrev graphFundamentalGroup {V : Type u} [Quiver.{u} V] (root : V) :=
  End ((Quiver.FreeGroupoid.of V).obj root)

abbrev graphTree {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V))) :=
  @geodesicSubtree
    (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
    (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
    ((Quiver.FreeGroupoid.of V).obj root)
    (inferInstance : @RootedConnected
      (Symmetrify (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)))
      ((Quiver.FreeGroupoid.of V).obj root))

def generatorTotalEquiv {V : Type u} [Quiver.{u} V] :
    Quiver.Total (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)) ≃
      Quiver.Total V where
  toFun e := ⟨e.left.as, e.right.as, e.hom⟩
  invFun e := ⟨(Quiver.FreeGroupoid.of V).obj e.left,
    (Quiver.FreeGroupoid.of V).obj e.right, e.hom⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-! The complement of the geodesic tree is the set of non-tree generators.  It
    is deliberately indexed by actual generator arrows rather than by an
    anonymous cardinal, so the resulting basis can be used in later proofs. -/
noncomputable def graphGeneratorSet {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Set (Quiver.Total (IsFreeGroupoid.Generators (Quiver.FreeGroupoid V))) :=
  (wideSubquiverEquivSetTotal
    (wideSubquiverSymmetrify (graphTree root)))ᶜ

lemma graphGeneratorSet_card {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Fintype.card (graphGeneratorSet root) =
      edgeCount (V := V) + 1 - vertexCount (V := V) := by
  classical
  let G := IsFreeGroupoid.Generators (Quiver.FreeGroupoid V)
  let T := graphTree root
  let S : Set (Quiver.Total G) :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  letI : Fintype S := setSubtypeFintype S
  letI : Fintype (Sᶜ : Set (Quiver.Total G)) := setSubtypeFintype Sᶜ
  have hGcard : Fintype.card G = Fintype.card V :=
    Fintype.card_congr generatorObjEquiv
  have hS : Fintype.card S = Fintype.card V - 1 := by
    have hS' := symmetrified_tree_set_card T
    rw [hGcard] at hS'
    simpa [S, T] using hS'
  have htotal : Fintype.card (Quiver.Total G) = Fintype.card (Quiver.Total V) :=
    Fintype.card_congr generatorTotalEquiv
  have hcomp : Fintype.card (Sᶜ : Set (Quiver.Total G)) =
      Fintype.card (Quiver.Total G) - Fintype.card S := by
    exact @Fintype.card_subtype_compl _ _ (fun e : Quiver.Total G => e ∈ S)
      (setSubtypeFintype S) (setSubtypeFintype Sᶜ)
  have htreele : Fintype.card S ≤ Fintype.card (Quiver.Total G) := by
    exact Fintype.card_subtype_le _
  have htreele' : Fintype.card V - 1 ≤ Fintype.card (Quiver.Total V) := by
    rw [← hS, ← htotal]
    exact htreele
  have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  change Fintype.card (Sᶜ : Set (Quiver.Total G)) =
    edgeCount (V := V) + 1 - vertexCount (V := V)
  rw [hcomp, htotal, hS]
  change Fintype.card (Quiver.Total V) - (Fintype.card V - 1) =
    Fintype.card (Quiver.Total V) + 1 - Fintype.card V
  omega

/-! The final theorem is kept in the original statement form for the Palomar
    Challenge/Solution correspondence.  The reusable, basis-valued API and
    the consequences of the computation live in `Consequences.lean`. -/

theorem proved_graph_fundamental_group_free_rank {V : Type u} [Quiver.{u} V]
    [Fintype V] [FiniteQuiver V] [WeaklyConnected V] (root : V) :
    Nonempty (graphFundamentalGroup root ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  classical
  let B : FreeGroupBasis (graphGeneratorSet root) (graphFundamentalGroup root) := by
    simpa [graphGeneratorSet] using! (spanningTreeBasis (graphTree root))
  have hcard := graphGeneratorSet_card root
  let eX : graphGeneratorSet root ≃
      Fin (edgeCount (V := V) + 1 - vertexCount (V := V)) :=
    hcard ▸ Fintype.equivFin (graphGeneratorSet root)
  exact ⟨(B.reindex eX).repr⟩

end FiniteGraphFreeGroup
