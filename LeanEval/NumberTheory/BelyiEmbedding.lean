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

namespace LeanEval.NumberTheory.BelyiEmbedding

open CategoryTheory

universe u

namespace ProfiniteGrp

/-- Conjugation by an element of a profinite group, as an automorphism in `ProfiniteGrp`. -/
def conjugationIso (G : ProfiniteGrp.{u}) (g : G) : Aut G :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso
    (ContinuousMulEquiv.mk (MulAut.conj g) (IsTopologicalGroup.continuous_conj g))

/-- The outer automorphism group of a profinite group. -/
abbrev OuterAutomorphismGroup (G : ProfiniteGrp.{u}) :=
  Aut G ⧸ Subgroup.normalClosure (Set.range (conjugationIso G))

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

end LeanEval.NumberTheory.BelyiEmbedding
