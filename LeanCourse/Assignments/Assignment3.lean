import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  apply h1
  exact h2
}



/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  intro ε hε
  specialize hs ε hε
  obtain ⟨N, hN⟩ := hs
  specialize hr N
  obtain ⟨N1, hN1⟩ := hr
  use N1
  intro n hn
  specialize hN1 n hn
  specialize hN (r n) hN1
  simp
  exact hN
}

/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  intro ε hε
  specialize hs₁ ε hε
  obtain ⟨N1, hN1⟩ := hs₁
  specialize hs₃ ε hε
  obtain ⟨N3, hN3⟩ := hs₃
  let N2 := max N1 N3
  use N2
  intro n hn
  specialize hN1 n (le_of_max_le_left hn)
  specialize hN3 n (le_of_max_le_right hn)
  rw [abs_lt]
  constructor
  · rw [abs_lt] at hN1
    specialize hs₁s₂ n
    calc -ε
       < s₁ n - a := by apply hN1.1
      _ ≤ s₂ n - a := by linarith
  · rw [abs_lt] at hN3
    specialize hs₂s₃ n
    calc s₂ n - a
       ≤ s₃ n - a := by linarith
      _ < ε := by apply hN3.2
}



/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by {
  intro ε hε
  simp
  use (⌈(1/ε)-1⌉₊ + 1)
  intro n hn
  rw [abs_lt]
  constructor
  · calc -ε < 0 := by linarith
          _ < (↑n + 1)⁻¹ := by exact inv_pos_of_nat
  · have h : 1 / ε - 1 < n := by exact lt_of_ceil_lt hn
    have h1 : 1 / ε < n +1 := by exact sub_lt_iff_lt_add.mp h
    rw [← one_div]
    rw [one_div_lt]
    assumption
    exact cast_add_one_pos n
    assumption
}

/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by {
  let s₁ : ℕ → ℝ :=  fun n ↦ (-1) / (n+1)
  let s₂ : ℕ → ℝ :=  fun n ↦ sin n / (n+1)
  let s₃ : ℕ → ℝ :=  fun n ↦ 1 / (n+1)
  have hs₁s₂ : ∀ n , s₁ n ≤ s₂ n := by {
    intro n
    simp
    rw [div_le_div_right]
    exact neg_one_le_sin ↑n
    exact cast_add_one_pos n
  }
  have hs₂s₃ : ∀ n , s₂ n ≤ s₃ n := by {
    intro n
    simp
    rw [← one_div,div_le_div_right]
    exact sin_le_one ↑n
    exact cast_add_one_pos n
  }
  have h : SequentialLimit s₂ 0 := by {
    apply exercise3_3 use_me exercise3_4 hs₁s₂ hs₂s₃
  }
  exact h
}

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by {
  by_contra hn
  push_neg at hn
  obtain ⟨n, hn1⟩ := hn
  specialize h1 (u n - l) (by linarith)
  obtain ⟨N₁,hN₁⟩ := h1
  specialize hN₁ (max n N₁) (by exact Nat.le_max_right n N₁)
  have hp : u (max n N₁) - l ≥ u n - l := by {
    gcongr
    specialize h2 n (max n N₁) (by exact Nat.le_max_left n N₁)
    exact h2
  }
  have hp1: u (max n N₁) - l < u n - l := by {
    rw [abs_lt] at hN₁
    exact hN₁.2
  }
  linarith
}




/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
      ext x
      simp
      constructor
      · intro h
        obtain ⟨ h1 , h2 ⟩ := h
        obtain ⟨ x₁ , hx ⟩  := h1
        use x₁
        obtain ⟨ h3 , h4⟩ := hx
        subst x
        constructor
        · constructor
          assumption
          assumption
        · rfl
      · intro h
        obtain ⟨ x₁ , h1 ⟩ := h
        obtain ⟨ h2 , h3 ⟩ := h1
        subst x
        constructor
        · use x₁
          constructor
          exact h2.1
          rfl
        · exact h2.2
}

lemma exercise3_8 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by {
  ext x
  simp
  constructor
  · intro h1
    by_contra hp
    push_neg at hp
    rw [← abs_lt] at hp
    have h2 : 4 > x ^ 2 := by
      calc 4 = 2 * 2 := by norm_num
           _ > |x| * |x| := by gcongr
           _ = x * x := by simp
           _ = x ^ 2 := by rw [@sq]
    linarith
  · intro h1
    rw [← le_abs'] at h1
    calc 4 = 2 * 2 := by norm_num
         _ ≤ |x| * |x| := by gcongr
         _ = x * x := by simp
         _ = x ^ 2 := by rw [@sq]
}



/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/

lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff

  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ sorry
  let R : Set γ → Set α × Set β :=
    fun s ↦ sorry
  sorry
