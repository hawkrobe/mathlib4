/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

## Main definitions

* `DirectSum.Decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `DirectSum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `DirectSum.Decomposition.isInternal`: The link to `DirectSum.IsInternal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `DirectSum.decompose`, instead making copies for the
`AddEquiv`, `LinearEquiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/

@[expose] public section


variable {ι R M σ : Type*}

open DirectSum

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

/-- A decomposition is an equivalence between an additive monoid `M` and a direct sum of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This definition also
works for additive groups and modules.

This is a version of `DirectSum.IsInternal` which comes with a constructive inverse to the
canonical "recomposition" rather than just a proof that the "recomposition" is bijective.

Often it is easier to construct a term of this type via `Decomposition.ofAddHom` or
`Decomposition.ofLinearMap`. -/
class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'

/-- `DirectSum.Decomposition` instances, while carrying data, are always equal. -/
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y ↦ by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

/-- A convenience method to construct a decomposition from an `AddMonoidHom`, such that the proofs
of left and right inverse can be constructed via `ext`. -/
abbrev Decomposition.ofAddHom (decompose : M →+ ⨁ i, ℳ i)
    (h_left_inv : (DirectSum.coeAddMonoidHom ℳ).comp decompose = .id _)
    (h_right_inv : decompose.comp (DirectSum.coeAddMonoidHom ℳ) = .id _) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

/-- Noncomputably conjure a decomposition instance from a `DirectSum.IsInternal` proof. -/
@[instance_reducible]
noncomputable def IsInternal.chooseDecomposition (h : IsInternal ℳ) :
    DirectSum.Decomposition ℳ where
  decompose' := (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv

variable [Decomposition ℳ]

protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
to a direct sum of components. This is the canonical spelling of the `decompose'` field. -/
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv

omit [AddSubmonoidClass σ M] in
/-- A substructure `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous components
  of `m` are in `p`. -/
def SetLike.IsHomogeneous {P : Type*} [SetLike P M] (p : P) : Prop :=
  ∀ (i : ι) ⦃m : M⦄, m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p

@[elab_as_elim]
protected theorem Decomposition.inductionOn {motive : M → Prop} (zero : motive 0)
    (homogeneous : ∀ {i} (m : ℳ i), motive (m : M))
    (add : ∀ m m' : M, motive m → motive m' → motive (m + m')) : ∀ m, motive m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  have t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (decompose ℳ).left_inv _
      right_inv := fun _ ↦ (decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ homogeneous ⟨m, h⟩) zero add
--  exact fun m ↦
--    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add

@[simp]
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ := rfl

@[simp]
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _

@[simp]
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of _, Equiv.apply_symm_apply]

theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩

theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (decompose ℳ x i : M) = x := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]

theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j : M) = 0 := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ hij.symm, ZeroMemClass.coe_zero]

theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x ∈ ℳ i) (hxj : x ∈ ℳ j) (hx : x ≠ 0) :
    i = j := by
  contrapose! hx; rw [← decompose_of_mem_same ℳ hxj, decompose_of_mem_ne ℳ hxi hx]

#adaptation_note
/--
`simps!` won't apply `AddEquiv.symm_mk` without the `id <|` in `map_add'`.
`decompose` and `Equiv.symm` are not implicit-reducible, so the type of the proof doesn't match the
expected type up to implicit reducibility. If we remove `id`, we don't get an immediate error,
but some downstream declarations will break.
-/
/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
@[simps!]
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with
    map_add' := id <| map_add (DirectSum.coeAddMonoidHom ℳ) }

@[simp]
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)

@[simp]
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm

@[simp]
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y

@[simp]
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y

@[simp]
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    decompose ℳ (∑ i ∈ s, f i) = ∑ i ∈ s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s

@[simp]
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i ∈ s, f i) = ∑ i ∈ s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s

theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i ∈ (decompose ℳ r).support, (decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r, ← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]

theorem AddSubmonoidClass.IsHomogeneous.mem_iff
    {P : Type*} [SetLike P M] [AddSubmonoidClass P M] (p : P)
    (hp : SetLike.IsHomogeneous ℳ p) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p := by
  classical
  refine ⟨fun hx i ↦ hp i hx, fun hx ↦ ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ ↦ hx i)

theorem AddSubmonoidClass.IsHomogeneous.ext
    {ℳ : ι → σ} [Decomposition ℳ] {P : Type*} [SetLike P M] [AddSubmonoidClass P M]
    {p q : P} (hp : SetLike.IsHomogeneous ℳ p) (hq : SetLike.IsHomogeneous ℳ q)
    (hpq : ∀ i, ∀ m ∈ ℳ i, m ∈ p ↔ m ∈ q) :
    p = q := by
  refine SetLike.ext fun m ↦ ?_
  rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp,
    AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i ↦ hpq i _ (decompose ℳ _ i).2

end AddCommMonoid

section AddCommGroup

variable [DecidableEq ι] [AddCommGroup M]
variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)
variable [Decomposition ℳ]

@[simp]
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x

@[simp]
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x

@[simp]
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y

@[simp]
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y

end AddCommGroup

section Module

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M)

/-- A convenience method to construct a decomposition from an `LinearMap`, such that the proofs
of left and right inverse can be constructed via `ext`. -/
abbrev Decomposition.ofLinearMap (decompose : M →ₗ[R] ⨁ i, ℳ i)
    (h_left_inv : DirectSum.coeLinearMap ℳ ∘ₗ decompose = .id)
    (h_right_inv : decompose ∘ₗ DirectSum.coeLinearMap ℳ = .id) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

variable [Decomposition ℳ]

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
a module to a direct sum of components. -/
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }

theorem decomposeLinearEquiv_apply (m : M) :
    decomposeLinearEquiv ℳ m = decompose ℳ m := rfl

theorem decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) :
    (decomposeLinearEquiv ℳ).symm m = (decompose ℳ).symm m := rfl

@[simp]
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x

@[simp] theorem decomposeLinearEquiv_symm_comp_lof (i : ι) :
    (decomposeLinearEquiv ℳ).symm ∘ₗ lof R ι (ℳ ·) i = (ℳ i).subtype :=
  LinearMap.ext <| decompose_symm_of _

@[simp] lemma decomposeLinearEquiv_symm_lof (i : ι) (x : ℳ i) :
    (decomposeLinearEquiv ℳ).symm (lof R _ _ i x) = x :=
  congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)

@[simp] lemma decomposeLinearEquiv_apply_coe (i : ι) (x : ℳ i) :
    decomposeLinearEquiv ℳ x = lof R _ _ i x :=
  (LinearEquiv.eq_symm_apply _).mp (decomposeLinearEquiv_symm_lof ..).symm

/-- Two linear maps from a module with a decomposition agree if they agree on every piece.

Note this cannot be `@[ext]` as `ℳ` cannot be inferred. -/
theorem decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M →ₗ[R] N⦄
    (h : ∀ i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g :=
  LinearMap.ext <| (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr <|
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) →ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeLinearEquiv_symm_comp_lof ℳ i, h]

end Module

section FiberSup

variable {κ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
variable (f : ι → κ) (ℳ : ι → Submodule R M)

/-- The pushforward along `f : ι → κ` of a family of submodules indexed by `ι`: the piece at
`j : κ` is the supremum of the pieces in the fiber of `f` over `j`. A decomposition pushes
forward to a decomposition (`DirectSum.fiberSup.decomposition`); this is the internal
counterpart of the index-side regrouping `DirectSum.sigmaFiberAddEquiv`. -/
def fiberSup (j : κ) : Submodule R M :=
  ⨆ i ∈ f ⁻¹' {j}, ℳ i

theorem le_fiberSup (i : ι) : ℳ i ≤ fiberSup f ℳ (f i) :=
  le_biSup ℳ rfl

theorem fiberSup_le {j : κ} {p : Submodule R M} :
    fiberSup f ℳ j ≤ p ↔ ∀ i, f i = j → ℳ i ≤ p := by
  simp [fiberSup, iSup_le_iff, Set.mem_preimage]

theorem mem_fiberSup_of_mem {i : ι} {x : M} (hx : x ∈ ℳ i) : x ∈ fiberSup f ℳ (f i) :=
  le_fiberSup f ℳ i hx

theorem fiberSup_eq_iSup_subtype (j : κ) : fiberSup f ℳ j = ⨆ i : { i // f i = j }, ℳ i := by
  rw [fiberSup, iSup_subtype']
  rfl

variable [DecidableEq ι] [DecidableEq κ] [Decomposition ℳ]

open LinearMap in
/-- The decomposition map into the pushforward pieces: decompose along `ℳ`, then send the
`i` component into the `f i` summand. -/
private def fiberSup.decomposeAux : M →ₗ[R] ⨁ j, fiberSup f ℳ j :=
  (toModule R ι _ fun i ↦
      lof R κ (fun j ↦ fiberSup f ℳ j) (f i) ∘ₗ Submodule.inclusion (le_fiberSup f ℳ i)) ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap

private theorem fiberSup.decomposeAux_coe {i : ι} (x : ℳ i) :
    fiberSup.decomposeAux f ℳ (x : M) =
      lof R κ (fun j ↦ fiberSup f ℳ j) (f i) ⟨x, mem_fiberSup_of_mem f ℳ x.2⟩ := by
  simp only [fiberSup.decomposeAux, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    decomposeLinearEquiv_apply, decompose_coe, ← lof_eq_of R, toModule_lof]
  rfl

private theorem fiberSup.coeLinearMap_comp_decomposeAux :
    coeLinearMap (fiberSup f ℳ) ∘ₗ fiberSup.decomposeAux f ℳ = .id := by
  rw [fiberSup.decomposeAux, ← LinearMap.comp_assoc, ← LinearEquiv.eq_comp_toLinearMap_symm]
  refine linearMap_ext _ fun i ↦ ?_
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, lof_eq_of, LinearMap.id_comp,
    decomposeLinearEquiv_symm_comp_lof, Submodule.subtype_apply]
  rw [← lof_eq_of R, toModule_lof]
  simp [lof_eq_of, coeLinearMap_of]

/-- A decomposition indexed by `ι` pushes forward along `f : ι → κ` to a decomposition into
the fiberwise suprema `fiberSup f ℳ`. -/
@[no_expose] instance fiberSup.decomposition : Decomposition (fiberSup f ℳ) := by
  refine .ofLinearMap _ (fiberSup.decomposeAux f ℳ)
    (fiberSup.coeLinearMap_comp_decomposeAux f ℳ)
    (linearMap_ext _ fun j ↦ LinearMap.ext fun z ↦ ?_)
  have h0 : ∀ m ≠ j, fiberSup.decomposeAux f ℳ (z : M) m = 0 := by
    intro m hm
    rw [apply_eq_component R]
    refine (fiberSup_le f ℳ (p := LinearMap.ker
      (component R κ (fun j ↦ ↥(fiberSup f ℳ j)) m ∘ₗ fiberSup.decomposeAux f ℳ))).2 ?_ z.2
    rintro i rfl x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply,
      fiberSup.decomposeAux_coe f ℳ (⟨x, hx⟩ : ℳ i), component.of]
    exact dif_neg (Ne.symm hm)
  have hz : fiberSup.decomposeAux f ℳ (z : M) =
      lof R κ (fun j ↦ ↥(fiberSup f ℳ j)) j (fiberSup.decomposeAux f ℳ (z : M) j) := by
    refine DFinsupp.ext fun m ↦ ?_
    rcases eq_or_ne m j with rfl | hm
    · simp
    · simp [h0 m hm, lof_eq_of, of_eq_of_ne _ _ _ hm]
  have h1 : coeLinearMap (fiberSup f ℳ) (fiberSup.decomposeAux f ℳ (z : M)) = (z : M) :=
    DFunLike.congr_fun (fiberSup.coeLinearMap_comp_decomposeAux f ℳ) (z : M)
  rw [hz] at h1
  have key : fiberSup.decomposeAux f ℳ (z : M) = lof R κ _ j z :=
    hz.trans (congrArg _ (Subtype.ext (by simpa [lof_eq_of] using h1)))
  simpa [lof_eq_of] using key

/-- The pushforward of a decomposition is internal. -/
theorem fiberSup.isInternal : IsInternal (fiberSup f ℳ) :=
  Decomposition.isInternal _

end FiberSup

end DirectSum
