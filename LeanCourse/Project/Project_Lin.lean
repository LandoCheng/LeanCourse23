import LeanCourse.Common

import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homotopy.Basic

import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import Mathlib.Geometry.Euclidean.Sphere.Basic

import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic



open BigOperators Function Set Filter Topology TopologicalSpace MeasureTheory MetricSpace EuclideanGeometry
open Real Classical

noncomputable section

/- 1.to define covering space -/

def MapExtend {E : Type*} {X :Type*} (S : Set X)
    (f : E → S) (x : E): X := f x

class CoveringSpace (X : Type*) [TopologicalSpace X] (E : Type*) [TopologicalSpace E]
    where
  pr : E → X
  Continuity : Continuous pr
  Cover : Set (Set X)
  IsOpenCover : (∀ U ∈ Cover, IsOpen U)  ∧  (univ = ⋃₀ Cover)
  Sheet : Cover → Set (Set E)
  SheetDef : ∀ (U : Cover), ( ∀ V ∈ Sheet U, IsOpen V ) ∧
            ( ∀ V₁ ∈ Sheet U , ∀ V₂ ∈ Sheet U, V₁ ≠ V₂ → V₁ ∩ V₂ = ∅) ∧
            ( ∀ V ∈ Sheet U , (pr '' V) = U ∧ ∃ f : V ≃ₜ U ,
                              MapExtend (U : Set X) (fun (x : V) ↦ f x ) = restrict V pr)



/- 2.to define a covering space ℝ → S¹ -/

notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

def Circle := { p : ℝ² | ‖p‖  = 1 }

notation "S¹" => Circle


lemma NegOneInS : (show ℝ² from ![-1,0]) ∈ S¹ := by
  simp [Circle, EuclideanSpace.norm_eq]
def rS : Set S¹ := { ⟨ ![-1,0] , NegOneInS ⟩ }ᶜ

lemma PostOneInS : (show ℝ² from ![1,0]) ∈ S¹ := by
  simp [Circle, EuclideanSpace.norm_eq]
def lS : Set S¹ := { ⟨ ![1,0] , PostOneInS ⟩ }ᶜ

example (x : S¹) (h: x = { val := ![-1, 0], property := NegOneInS }) : (x : ℝ²) = ![-1,0] := by
  apply Subtype.coe_eq_iff.2
  use NegOneInS


lemma Univ_eq_Union : univ = rS ∪ lS := by {
  ext x
  simp
  rw [rS, lS]
  simp
  by_cases h : (x : ℝ²) ≠ ![-1,0]
  · left
    exact Subtype.ne_of_val_ne h
  · right
    simp at h
    have : (x : ℝ²) ≠ ![1,0] := by
      calc (x : ℝ²) = ![-1,0] := h
        _ ≠ ![1,0] := by rw [Function.ne_iff]; use 0; simp
    exact Subtype.ne_of_val_ne this
}


def Collection1 : Set (Set ℝ) := { Ioo ((i : ℝ) - 2⁻¹) (i + 2⁻¹) | i : ℤ }
def Collection2 : Set (Set ℝ) := { Ioo (i : ℝ) (i + 1) | i : ℤ }



noncomputable instance RtoS : CoveringSpace S¹ ℝ where
  pr := fun (x : ℝ) ↦ ⟨![Real.cos (2 * π * x), Real.sin (2 * π * x)],
    by simp [Circle,EuclideanSpace.norm_eq]⟩
  Continuity := by
    apply Continuous.codRestrict
    apply continuous_pi
    intro i
    fin_cases i
    · simp
      continuity
    · simp
      continuity
  Cover := { rS , lS }
  IsOpenCover := by
    constructor
    · intro U hU
      simp at hU
      obtain hr|hl := hU
      · rw [hr,rS]
        simp
        apply Set.Finite.isClosed
        simp
      · rw [hl,lS]
        simp
        apply Set.Finite.isClosed
        simp
    · simp
      apply Univ_eq_Union
  Sheet := fun U ↦ if ((U : Set S¹) = rS) then Collection1 else Collection2
  SheetDef := by
    intro U
    by_cases (U = rS)
    · constructor
      · simp [h]
        intro V hV
        simp [Collection1] at hV
        obtain ⟨i, hV⟩ := hV
        subst V
        exact isOpen_Ioo
      constructor
      · simp [h]
        intro V₁ hV₁ V₂ hV₂
        simp [Collection1] at hV₁ hV₂
        obtain ⟨i₁,hV₁⟩ := hV₁
        obtain ⟨i₂,hV₂⟩ := hV₂
        intro hp
        subst V₁ V₂
        have hi : (i₁ : ℝ) ≠ i₂ := by
        {
          by_contra nhi
          rw [nhi] at hp
          simp at hp
        }
        ext x
        simp
        intro hx1 hx2 hx3
        have hi1 : (i₂ : ℝ) - 2⁻¹ < i₁ + 2⁻¹ := by linarith
        rw [sub_lt_iff_lt_add,add_assoc] at hi1
        norm_num at hi1
        have hi2 : (i₂ : ℝ) < i₁ := by {
          by_contra hi3
          push_neg at hi3
          have hi4 : (i₁ : ℝ) < i₂ := by
            rw [lt_iff_le_and_ne]
            exact ⟨hi3 , hi⟩
          have hi5 : i₁ ≤ i₂ - 1 := by
            apply Int.le_sub_one_iff.2
            norm_cast at hi4
          have hi5 : (i₁ : ℝ) ≤ i₂ - 1 := by norm_cast
          rw [le_sub_iff_add_le] at hi5
          linarith
        }
        have hi3 : i₂ ≤ i₁ - 1 := by
          apply Int.le_sub_one_iff.2
          norm_cast at hi2
        have hi3 : (i₂ : ℝ) ≤ i₁ - 1 := by norm_cast
        calc  (i₂ : ℝ) + 2⁻¹ ≤ i₁ - 1 + 2⁻¹ := by linarith
              _= i₁ - 2⁻¹ := by rw [sub_add]; norm_num
              _≤ x := le_of_lt hx1
      · simp [h]
        intro V hV
        simp [Collection1] at hV
        obtain ⟨i , hV⟩ := hV
        constructor
        · ext x
          simp
          constructor
          · intro ⟨x₁, ⟨ h1x₁, h2x₁⟩ ⟩
            symm at h2x₁
            have h3x₁ : x = show ℝ² from ![cos (2 * π * x₁), sin (2 * π * x₁)] := by
              apply Subtype.coe_eq_iff.2
              sorry
            sorry
          · sorry
        · sorry
    · constructor
      · simp [h]
        sorry
      constructor
      · sorry
      · sorry



/- 4.homtopy properties -/




/- 5.ℤ ≃* π₁(S¹,(1,0)) -/


lemma BasedPoint_of_S : (show ℝ² from ![1,0]) ∈ S¹ := by
  simp [Circle,EuclideanSpace.norm_eq]

noncomputable instance : FundamentalGroup S¹ ⟨![1,0] , BasedPoint_of_S ⟩  where
  hom := sorry
  inv := sorry

--theorem Z_Iso_FundamentalGroup_of_Circle : ℤ ≃*
