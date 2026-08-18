import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import EvalTools.Markers

/-!
# The absolute Galois group of the rationals embeds in `Out(\widehat{F}_2)`

The arithmetic étale fundamental-group sequence for `X = ℙ¹_ℚ \ {0, 1, ∞}` induces a
continuous outer representation

`Gal(ℚ̄/ℚ) → Out(π₁(X_{ℚ̄})) ≅ Out(\widehat{F}_2)`.

Belyi's theorem implies that this representation is injective: finite étale covers of `X_{ℚ̄}`
correspond to conjugacy classes of open subgroups of `\widehat{F}_2`, and every algebraic curve
over `ℚ̄` is birational to such a cover. We therefore call the resulting injection

`Gal(ℚ̄/ℚ) ↪ Out(\widehat{F}_2)`

the **Belyi embedding**.

Here `\widehat{F}_2` is modeled as the profinite completion of the free group on two generators.
The outer automorphism group is the categorical automorphism group of this profinite group modulo
its subgroup of inner automorphisms. Thus its automorphisms and their inverses are continuous. The
formal statement records the underlying injective group homomorphism; it does not record continuity
of the Belyi embedding because no topology is placed on `OuterAutomorphismGroup` here.

## Reference

Robert A. Kucharczyk, *On copies of the absolute Galois group in* `Out(\widehat{F}_2)`,
Proceedings of the American Mathematical Society **144** (2016), 2351–2359,
[doi:10.1090/proc/12917](https://doi.org/10.1090/proc/12917), Introduction, equation (1) and the
corollary attributed to Belyi.
-/

set_option autoImplicit false

namespace LeanEval.NumberTheory.BelyiEmbedding

open CategoryTheory

noncomputable section

universe u

namespace ProfiniteGrp

@[simp]
lemma aut_one_hom_apply (G : ProfiniteGrp.{u}) (x : G) : (1 : Aut G).hom x = x := rfl

@[simp]
lemma aut_mul_hom_apply (G : ProfiniteGrp.{u}) (α β : Aut G) (x : G) :
    (α * β).hom x = α.hom (β.hom x) := rfl

@[simp]
lemma aut_inv_hom_apply (G : ProfiniteGrp.{u}) (α : Aut G) (x : G) :
    α⁻¹.hom x = α.inv x := rfl

/-- Conjugation by an element of a profinite group, as a continuous homomorphism. -/
@[simps! (attr := simp) toFun]
def conjugationHom (G : ProfiniteGrp.{u}) (g : G) : G →ₜ* G where
  toMonoidHom := (MulAut.conj g).toMonoidHom
  continuous_toFun := IsTopologicalGroup.continuous_conj g

/-- Conjugation by an element of a profinite group, as an automorphism in `ProfiniteGrp`. -/
@[simps (attr := simp)]
def conjugationIso (G : ProfiniteGrp.{u}) (g : G) : Aut G where
  hom := ProfiniteGrp.ofHom (conjugationHom G g)
  inv := ProfiniteGrp.ofHom (conjugationHom G g⁻¹)
  hom_inv_id := by
    ext x
    simp [mul_assoc]
  inv_hom_id := by
    ext x
    simp [mul_assoc]

/-- Conjugation by elements of a profinite group, regarded as categorical automorphisms. -/
@[simps (attr := simp)]
def innerAutomorphism (G : ProfiniteGrp.{u}) : G →* Aut G where
  toFun := conjugationIso G
  map_one' := by
    apply Aut.ext
    ext
    simp
  map_mul' g h := by
    apply Aut.ext
    ext
    simp [mul_assoc]

/-- The inner automorphisms form a normal subgroup of the automorphism group. -/
instance innerAutomorphismRangeNormal (G : ProfiniteGrp.{u}) :
    (innerAutomorphism G).range.Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ α
    refine ⟨α.hom g, ?_⟩
    apply Aut.ext
    ext x
    simpa [mul_assoc] using (ProfiniteGrp.hom_inv_apply α x).symm

/-- The outer automorphism group of a profinite group: its categorical automorphism group modulo
its inner automorphisms. -/
abbrev OuterAutomorphismGroup (G : ProfiniteGrp.{u}) :=
  Aut G ⧸ (innerAutomorphism G).range

end ProfiniteGrp

/-- The free profinite group on two generators, modeled as the profinite completion of the
(discrete) free group on `Fin 2`. -/
abbrev freeProfiniteGroupOnTwoGenerators : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (.mk (FreeGroup (Fin 2)))

/-- The **Belyi embedding**: the absolute Galois group of `ℚ` embeds in the outer automorphism
group of the free profinite group on two generators. Its existence is a consequence of Belyi's
theorem. -/
@[eval_problem]
theorem belyi_embedding :
    ∃ ρ : Field.absoluteGaloisGroup ℚ →*
      ProfiniteGrp.OuterAutomorphismGroup freeProfiniteGroupOnTwoGenerators,
      Function.Injective ρ := by
  sorry

end

end LeanEval.NumberTheory.BelyiEmbedding
