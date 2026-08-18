import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import EvalTools.Markers

/-!
# The absolute Galois group inside `Out(\widehat{F}_2)`

The faithful outer action of the absolute Galois group of `ℚ` on the geometric étale
fundamental group of `ℙ¹ \ {0, 1, ∞}` gives an embedding

`Gal(ℚ̄/ℚ) ↪ Out(\widehat{F}_2)`.

Here `\widehat{F}_2` is modeled as the profinite completion of the free group on two
generators. The definitions below model the outer automorphism group of a profinite group as
the group of continuous automorphisms modulo its subgroup of inner automorphisms.
-/

set_option autoImplicit false

namespace LeanEval.NumberTheory.BelyiEmbedding

open CategoryTheory

noncomputable section

universe u

namespace ProfiniteGrp

/-- Conjugation by an element of a profinite group, as an automorphism in `ProfiniteGrp`. -/
def conjugationIso (G : ProfiniteGrp.{u}) (g : G) : Aut G :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso {
    toMulEquiv := MulAut.conj g
    continuous_toFun := by
      change Continuous (fun x : G => g * x * g⁻¹)
      fun_prop
    continuous_invFun := by
      change Continuous (fun x : G => g⁻¹ * x * g)
      fun_prop
  }

/-- Conjugation by elements of a profinite group, regarded as categorical automorphisms. -/
def innerAutomorphism (G : ProfiniteGrp.{u}) : G →* Aut G where
  toFun := conjugationIso G
  map_one' := by
    apply Aut.ext
    ext x
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  map_mul' g h := by
    apply Aut.ext
    ext x
    change (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹
    group

/-- The inner automorphisms form a normal subgroup of the automorphism group. -/
instance innerAutomorphismRangeNormal (G : ProfiniteGrp.{u}) :
    (innerAutomorphism G).range.Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α.hom g, ?_⟩
    apply Aut.ext
    ext x
    change G ≅ G at α
    change α.hom g * x * (α.hom g)⁻¹ = α.hom (g * α.inv x * g⁻¹)
    simp only [map_mul, map_inv]
    rw [ProfiniteGrp.hom_inv_apply]

/-- The outer automorphism group of a profinite group: its categorical automorphism group modulo
its inner automorphisms. -/
abbrev OuterAutomorphismGroup (G : ProfiniteGrp.{u}) :=
  Aut G ⧸ (innerAutomorphism G).range

end ProfiniteGrp

/-- The free profinite group on two generators, modeled as the profinite completion of the
(discrete) free group on `Fin 2`. -/
abbrev freeProfiniteGroupOnTwoGenerators : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (.mk (FreeGroup (Fin 2)))

/-- The absolute Galois group of `ℚ` embeds in the outer automorphism group of the free profinite
group on two generators. -/
@[eval_problem]
theorem belyi_embedding :
    ∃ ρ : Field.absoluteGaloisGroup ℚ →*
      ProfiniteGrp.OuterAutomorphismGroup freeProfiniteGroupOnTwoGenerators,
      Function.Injective ρ := by
  sorry

end

end LeanEval.NumberTheory.BelyiEmbedding
