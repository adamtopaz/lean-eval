import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import EvalTools.Markers

/-!
# The absolute Galois group of the rationals embeds in `Out(\widehat{F}_2)`

The faithful outer action of the absolute Galois group of `ℚ` on the geometric étale
fundamental group of `ℙ¹ \ {0, 1, ∞}` gives an embedding

`Gal(ℚ̄/ℚ) ↪ Out(\widehat{F}_2)`.

We call this the **Belyi embedding** because its existence is a consequence of Belyi's theorem.

Here `\widehat{F}_2` is modeled as the profinite completion of the free group on two
generators. The outer automorphism group is the categorical automorphism group of this profinite
group modulo its subgroup of inner automorphisms.
-/

open CategoryTheory

universe u

namespace ProfiniteGrp

/-- Conjugation by an element of a profinite group, as an automorphism in `ProfiniteGrp`. -/
def conjugationIso (G : ProfiniteGrp.{u}) (g : G) : G ≅ G :=
  ContinuousMulEquiv.toProfiniteGrpIso <|
    .mk (MulAut.conj g) <| IsTopologicalGroup.continuous_conj g

@[simp] private lemma conjugationIso_hom_apply (G : ProfiniteGrp.{u}) (g x : G) :
    (conjugationIso G g).hom x = g * x * g⁻¹ := rfl

/-- Conjugation by elements of a profinite group. -/
def innerAutomorphism (G : ProfiniteGrp.{u}) : G →* Aut G :=
  MonoidHom.mk' (conjugationIso G) fun g h ↦
    Iso.ext (α := conjugationIso G (g * h))
      (β := (conjugationIso G h).trans (conjugationIso G g)) (by
        ext
        simp [mul_assoc])

/-- The inner automorphisms form a normal subgroup of the automorphism group. -/
instance innerAutomorphismRangeNormal (G : ProfiniteGrp.{u}) :
    (innerAutomorphism G).range.Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ (α : G ≅ G)
    refine ⟨α.hom g, ?_⟩
    apply Iso.ext (α := conjugationIso G (α.hom g))
      (β := α.symm.trans ((conjugationIso G g).trans α))
    rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_hom]
    ext x
    simp [mul_assoc]

/-- The outer automorphism group of a profinite group. -/
abbrev OuterAutomorphismGroup (G : ProfiniteGrp.{u}) :=
  Aut G ⧸ (innerAutomorphism G).range

/-- The free profinite group on two generators, modeled as the profinite completion of the
(discrete) free group on `Fin 2`. -/
abbrev freeOnTwoGenerators : ProfiniteGrp :=
  ProfiniteCompletion.completion <| .mk <| FreeGroup (Fin 2)

end ProfiniteGrp

namespace LeanEval.NumberTheory.BelyiEmbedding

open ProfiniteGrp

/-- The **Belyi embedding**: the absolute Galois group of `ℚ` embeds in the outer automorphism
group of the free profinite group on two generators. Its existence is a consequence of Belyi's
theorem. -/
@[eval_problem]
theorem belyi_embedding :
    ∃ ρ : Field.absoluteGaloisGroup ℚ →* OuterAutomorphismGroup freeOnTwoGenerators,
      Function.Injective ρ := by
  sorry

end LeanEval.NumberTheory.BelyiEmbedding
