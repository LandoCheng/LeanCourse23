import LeanCourse.Common
open Set Function Real
noncomputable section
set_option linter.unusedVariables false
variable {ι L : Type*}


/- ## Today: Functions

We cover sections 4.2 and 4.3 from Mathematics in Lean.

<<<<<<< HEAD
we will discuss sets:
* Set-builder notation: `{ x : X | p x}`;
* Unions/intersections: `⋃ i : ι, C i`, `⋃ i ∈ s, C i` or `⋃₀ C`;
* Images and preimages: `f ⁻¹' s` or `f '' s`;
We will also define the inverse of a function.-/
=======
/-
Last time we discussed negation `¬` (not), classical logic, sequences and sets.
-/

/- ## Proving two sets are equal

You can prove that two sets are equal by applying `subset_antisymm` or using the `ext` tactic.
-/


variable {α β : Type*} (x : α) (s t : Set α)

example : (fun x : ℝ ↦ x ^ 2) 3 = 10 := by
  simp only; sorry

/- We saw last time that we can prove that two sets are equal using `ext`. -/
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff, and_comm]

/- We can also use existing lemmas and `calc`. -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by
  calc (s ∪ tᶜ) ∩ t
      = (s ∩ t) ∪ (tᶜ ∩ t) := by rw [@inter_distrib_right]
    _ = (s ∩ t) ∪ ∅ := by rw [@compl_inter_self]
    _ = s ∩ t := by rw [@union_empty]
>>>>>>> 2619d9fd66da03f7b375841a83cdb8370b6d4083



/- # Exercises -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx
}

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  intro y hy
  specialize h y
  obtain ⟨x, hx, rfl⟩ := h
  rw [← mem_preimage] at hy
  exact mem_image_of_mem f hy
}

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  intro y hy
  simp at hy
  obtain ⟨x1, hx1⟩ := hy.1
  obtain ⟨x2, hx2⟩ := hy.2
  have h1 : f x1 = f x2 := by
   calc f x1
      = y :=  hx1.2
    _ = f x2 := by rw [← hx2.2]
  specialize h h1
  subst x2
  use x1
  constructor
  · simp
    constructor
    exact hx1.1
    exact hx2.1
  · exact hx1.2
}

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  ext x
  simp
  constructor
  · intro h1
    obtain ⟨x₀, h2, h3⟩ := h1
    obtain ⟨i₀, hi₀⟩ := h2
    use i₀
    use x₀
  · intro h1
    obtain ⟨i₀, x₀, h2⟩ := h1
    use x₀
    constructor
    · use i₀
      exact h2.1
    · exact h2.2
}

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  ext x
  simp
  constructor
  · intro hy
    obtain ⟨y₀, hx⟩ := hy
    subst x
    exact sq_nonneg y₀
  · intro hx
    use (sqrt x)
    exact sq_sqrt hx
}



/- # I.Inverse of a function.

Suppose we have a function `f : α → β`.
Can we find a inverse `g : β → α` of `f`?
Not without assuming that `f` is bijective.
But suppose we try, suppose that `∃ x, f x = y`, and we want to define `g y`.
It must be one of the `x` such that `f x = y`.
We can choose one such `x` using *the axiom of choice*. -/

section Inverse

variable (f : α → β)

#check Classical.choose
#check Classical.choose_spec
open Classical

def conditionalInverse (y : β) (h : ∃ x : α, f x = y) :
   α :=
  Classical.choose h

lemma invFun_spec (y : β) (h : ∃ x, f x = y) :
    f (conditionalInverse f y h) = y :=
  Classical.choose_spec h

/- We can now define the function by cases on whether it lies in the range of `f` or not. -/

variable [Inhabited α]
def inverse (f : α → β) (y : β) : α :=
  if h : ∃ x : α, f x = y then
    conditionalInverse f y h else
    default

local notation "g" => inverse f -- let's call this function `g`

/- We can now prove that `g` is a right-inverse if `f` is surjective
and a left-inverse if `f` is injective.
We use the `ext` tactic to show that two functions are equal. -/
example (hf : Surjective f) : f ∘ g = id := by
  ext y
  simp
  obtain ⟨x, rfl⟩ := hf y
  simp [inverse, invFun_spec]

example (hf : Injective f) : g ∘ f = id := by
  ext x
  simp [inverse]
  have h : ∀ x y : α, f x = f y ↔ x = y :=
  · intro x y
    exact hf.eq_iff
  apply hf
  simp [invFun_spec]

end Inverse



/- # II.Cantor's theorem

Let's prove Cantor's theorem: there is no surjective function from any set to its power set. -/

example : ¬ ∃ (α : Type*) (f : α → Set α), Surjective f := by sorry


/- In section 4.3 of MIL you can read the proof of the Cantor-Schröder-Bernstein theorem. -/

example {f : α → β} {g : β → α}
    (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  sorry -- see MIL
