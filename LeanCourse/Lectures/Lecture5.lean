import LeanCourse.Common
open Real Function
noncomputable section
set_option linter.unusedVariables false



/- ## Today: Logic (continued) and sets

We cover sections 3.3, 3.6 and 4.1 from Mathematics in Lean.

We will discuss negation `¬` (not), classical logic, sequences and sets.
-/



/- # I.Negation

1.1 The negation `¬ A` just means `A → False`, where `False` is a specific false statement.

1.2 We can use the same tactics as for implication:
`intro` to prove a negation, and `apply` to use one. -/

example {p : Prop} (h : p) : ¬ ¬ p := by {
  intro h2
  -- rw [Not] at h2
  exact h2 h
}

example {α : Type*} {p : α → Prop} :
    ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by {
  constructor
  · intro h x hx
    -- notice that "(¬∃ x, p x) → ∀ (x : α), ¬p x" is equal to
    -- "(¬∃ x, p x) → ∀ (x : α), ( p x → False )" , that's why "hx : px"
    apply h
    exact ⟨x, hx⟩
  · intro h h2
    obtain ⟨x, hx⟩ := h2
    specialize h x hx
    exact h
}

/-
1.3 We can use `exfalso` to use the fact that everything follows from `False`:
ex falso quod libet -/

example {p : Prop} (h : ¬ p) :
    p → 0 = 1 := by {
  intro h2
  specialize h h2
  exfalso
  assumption
}

/-
1.4 `contradiction` proves any goal when two hypotheses are contradictory. -/

example {p : Prop} (h : ¬ p) :
    p → 0 = 1 := by {
  intro h2
  contradiction
}

/-
1.5 We can use classical reasoning (with the law of the excluded middle) using
the following tactics. -/

/-
1.5.1 `by_contra h` start a proof by contradiction. (反证法)-/
example {p : Prop} (h : ¬ ¬ p) : p := by {
  by_contra h2
  exact h h2
}
example (p q : Prop) (h : ¬ q → ¬ p) : p → q := by {
  intro hp
  by_contra hnq
  exact h hnq hp
}

/-
1.5.2 `by_cases h : p` to start a proof by cases on statement `p` .(分类讨论)-/
example (p q r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by {
  by_cases hp : p
  · exact h1 hp
  · exact h2 hp
}

/-
1.5.3 `push_neg` to push negations inside quantifiers and connectives.-/
example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by {
  push_neg
  rfl
}
example {p q : Prop} :
    ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by {
  push_neg
  rfl
}

/-
1.6 Example: Sequential Limit-/

-- The sequence `u` of real numbers converges to `l`.
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
--`∀ ε > 0, ...` means `∀ ε, ε > 0 → ...`

example (u : ℕ → ℝ) (l : ℝ) :
    ¬ SequentialLimit u l ↔ ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≥ ε := by {
  rw [SequentialLimit]
  push_neg
  rfl
}

lemma sequentialLimit_unique (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by {
  intro hl hl'
  by_contra hll'
  have : |l - l'| > 0
  · apply abs_pos.2
    apply sub_ne_zero.2
    exact hll'
  rw [SequentialLimit] at hl hl'
  specialize hl (|l - l'| / 2) (by linarith)
  obtain ⟨N, hN⟩ := hl
  obtain ⟨N', hN'⟩ := hl' (|l - l'| / 2) (by linarith)
  let N₀ := max N N'
  specialize hN N₀ (Nat.le_max_left N N')
  specialize hN' N₀ (Nat.le_max_right N N')
  have : |l - l'| < |l - l'| := by
    calc |l - l'|
        = |l - u N₀ + (u N₀ - l')| := by ring
      _ ≤ |l - u N₀| + |u N₀ - l'| := by exact abs_add (l - u N₀) (u N₀ - l')
      _ = |u N₀ - l| + |u N₀ - l'| := by rw [abs_sub_comm]
      _ < |l - l'| := by linarith
  linarith
}



/- # Exercises

Prove the following without using `push_neg` or lemmas from the library.
You will need to use `by_contra` in the proof. -/

example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  · intro h1
    by_contra h2
    obtain ⟨x₀,hp⟩ := h1
    specialize h2 x₀
    exact h2 hp
  · intro h1
    by_contra h2
    apply h1
    intro x hp
    apply h2
    use x
}

/- `simp` will be useful to simplify the goal. -/
lemma convergesTo_const (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  rw [SequentialLimit]
  intro ε hε
  use 1
  intro n hn
  --rw [sub_self,abs_zero]
  simp
  linarith
}

/- The next exercise is harder, and you will probably not finish it during class. -/
lemma SequentialLimit.add {s t : ℕ → ℝ} {a b : ℝ}
    (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  intro ε hε
  specialize hs (ε/2) (by linarith)
  obtain ⟨N1,hN1⟩ := hs
  specialize ht (ε/2) (by linarith)
  obtain ⟨N2,hN2⟩ := ht
  let N₀ := max N1 N2
  use N₀
  intro n hn
  have h1 : n ≥ N1 := by
   calc n ≥ N₀ := hn
        _ ≥ N1 := (le_max_left N1 N2)
  have h2 : n ≥ N2 := by
   calc n ≥ N₀ := hn
        _ ≥ N2 := (le_max_right N1 N2)
  specialize hN1 n h1
  specialize hN2 n h2
  simp
  calc  |s n + t n - (a+b)|
      = |s n - a + (t n - b)| := by ring
    _ ≤ |s n -a| + |t n - b| := by exact abs_add (s n - a) (t n - b)
    _ < ε := by linarith
}



/- # II.Sets

In set theory you can make sets with arbitrary elements.
But in Lean, all sets have to be sets of elements from a specific type.-/

#check Set ℕ
#check Set ℝ
-- example (r : ℕ) (s : Set ℝ) : r ∈ s := _

/-
2.1 to type some common set operations -/

variable {α β ι : Type*} (x : α) (s t : Set α)

#check x ∈ s       -- \in or \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub

#check s ∩ t       -- \inter or \cap
#check s ∪ t       -- \union or \cup
#check s \ t       -- it is the normal symbol `\` on your keyboard,
                   -- but you have to write `\\` or `\ ` to enter it
#check sᶜ          -- \compl or \^c
#check (∅ : Set α) -- \empty

-- we use "univ" to type the universial set rather than α directly
#check (Set.univ : Set α)

open Set
#check (univ : Set α)

/-
2.2 set operations and logic operations-/

/- Showing that `x` is an elements of `s ∩ t`, `s ∪ t` or `sᶜ`
corresponds by definition to conjunction, disjunction or negation. -/

#check mem_inter_iff
#check mem_union
#check mem_compl_iff

/- There are various ways to prove this:
* use lemma `mem_inter_iff`
* use `simp`
* directly apply `constructor`
* give a direct proof: `exact ⟨xs, xt⟩`
-/
example (hxs : x ∈ s) (hxt : x ∈ t) :
    x ∈ s ∩ t := by {
  -- rw [mem_inter_iff]
   simp [hxs, hxt]
  -- exact ⟨hxs, hxt⟩
}

example (hxs : x ∈ s) : x ∈ s ∪ t := by {
  left
  assumption
}

/-
2.3 Examples for set inclusion
`s ⊆ t` means that for every element `x` in `s`, `x` is also an element in `t`. -/

#check subset_def

example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  intro x hx
  constructor
  · exact hx.1
  · left
    exact hx.2

/- you can also prove it at the level of sets, without talking about elements.
!!!  pay attention to "gcongr" here -/
example : s ∩ t ⊆ s ∩ (t ∪ u) := by {
  gcongr
  exact subset_union_left t u
}

/-
2.4 Proving two Sets are equal
You can prove that two sets are equal by applying `subset_antisymm` or using the `ext` tactic.-/

#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)

example : s ∩ t = t ∩ s := by {
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    obtain ⟨h1x, h2x⟩ := hx
    constructor
    · exact h2x
    · exact h1x
}

/- We can also use existing lemmas and `calc`. -/
example : (s ∪ tᶜ) ∩ t = s ∩ t := by {
calc  (s ∪ tᶜ) ∩ t
  = (s ∩ t) ∪ (tᶜ ∩ t) := by exact inter_distrib_right s tᶜ t
_ = (s ∩ t) ∪ ∅  := by rw [compl_inter_self]
_ = s ∩ t := by exact union_empty (s ∩ t)
}


/-
2.5 Set-builder Notation-/

/- We can write `{x : α | p x}` to write the set of all elements in `α`
where `p` holds. -/
def Evens : Set ℕ := {n : ℕ | Even n}
def Odds : Set ℕ := {n | ¬ Even n}

example : Evens ∪ Odds = univ := by {
  ext n
  simp [Evens, Odds]
  exact em (Even n)
}

example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
-- alternative notation:
example : s ∩ t = {x ∈ s | x ∈ t} := by rfl

/- All set operators can be written using the set-builder notation. -/
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x | x ∉ s} := by rfl
example : (∅ : Set α) = {x | False} := by rfl
example : (univ : Set α) = {x | True} := by rfl


/-
2.6 Power Set -/

example (s : Set α) : 𝒫 s = {t | t ⊆ s} := by rfl -- \powerset

/- What is the type of `𝒫 s`?
Answer: Set (Set α)
compare with set theory:
if `s ⊆ ℝ` then s ∈ 𝒫 ℝ and 𝒫 s ∈ 𝒫 (𝒫 ℝ) -/

example (s t : Set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t := by ext; simp

/-
2.7 set operations for a family of sets -/

/-We can take unions and intersections of families of sets in two different ways:

2.7.1 index map
* Given a family of sets `C : ι → Set α`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements of `ι`.
-/
example (C : ι → Set α) : ⋃ i : ι, C i = {x : α | ∃ i : ι, x ∈ C i} := by ext; simp
-- "⋃ i : ι, C i" is to represent the union of this family of sets
example (C : ι → Set α) : ⋂ i : ι, C i = {x : α | ∀ i : ι, x ∈ C i} := by ext; simp

/-
* Given a family of sets `C : ι → Set α` and `s : Set ι`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements in `s`.
-/
example (s : Set ι) (C : ι → Set α) : ⋃ i ∈ s, C i = {x : α | ∃ i ∈ s, x ∈ C i} := by ext; simp
example (s : Set ι) (C : ι → Set α) : ⋂ i ∈ s, C i = {x : α | ∀ i ∈ s, x ∈ C i} := by ext; simp
example (s : Set ι) (C : ι → Set α) :
  ⋃ i : ι, ⋃ h : i ∈ s, C i = {x : α | ∃ i : ι, i ∈ s ∧ x ∈ C i} := by ext; simp

/-
2.7.2 subset of the power set
* Given a collection of sets `C : Set (Set α)`
  we can take the union and intersection of `c` for all `c ∈ C`-/
example (𝓒 : Set (Set α)) : ⋃₀ 𝓒 = {x : α | ∃ s ∈ 𝓒, x ∈ s} := by rfl
example (𝓒 : Set (Set α)) : ⋂₀ 𝓒 = {x : α | ∀ s ∈ 𝓒, x ∈ s} := by rfl
example (𝓒 : Set (Set α)) : ⋃₀ 𝓒 = ⋃ c ∈ 𝓒, c := by ext; simp

example (C : ι → Set α) (s : Set α) : s ∩ (⋃ i, C i) = ⋃ i, (C i ∩ s) := by
{
  ext x
  simp
  rw [@and_comm]
}

/-
2.8 images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`. -/

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl
example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl
-- f '' s can also written as { f x | x ∈ s}

example {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by {
  constructor
  · intro h x hx
    simp
    apply h
    exact mem_image_of_mem f hx
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    specialize h hx
    simp at h
    exact h
    /- another proof
    rw [mem_image] at hy
    obtain ⟨x₀, hx1, hx2⟩ := hy
    subst y
    specialize h hx1
    simp at h
    exact h -/
}
/-
* tactic "subst"
If you have a hypothesis `h : y = t` or `h : t = y`,
where `y` is a variable (and `t` anything),
then you can use `h` to substitute `y` by `t` everywhere, using the tactic `subst h` or `subst y`.
This can also be done by `obtain` and `intro` by naming the equality `rfl`.-/


/- We have another name for `f '' univ`, namely `range f`. -/
example (f : α → β) : f '' univ = range f := image_univ

/-
2.9 pointwise operations on sets. -/

open Pointwise

example (s t : Set ℝ) : s + t = {x : ℝ | ∃ a b, a ∈ s ∧ b ∈ t ∧ a + b = x } := by rfl
example (s t : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl

example : ({1, 3, 5} : Set ℝ) + {0, 10} = {1, 3, 5, 11, 13, 15} := by {
  ext x
  simp [mem_add]
  norm_num
  tauto
}
