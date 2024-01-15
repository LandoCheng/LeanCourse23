import LeanCourse.Common
open Set Function Real
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)



/- ## Today: Numbers and induction

We cover chapter 5 from Mathematics in Lean, and some material about `norm_cast`/`push_cast`
that is not covered in MiL. -/



/- # I.Recursion and induction

1.1 define factorical function recursively and prove related propositions inductively -/

/-Let's start by defining our own factorial function.
Note that there is no `:=` -/

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

-- illegal:
-- def wrong : ℕ → ℕ
--   | 0 => 1
--   | (n + 1) => wrong (n + 2)

lemma fac_zero : fac 0 = 1 := rfl
lemma fac_succ (n : ℕ) : fac (n + 1) = (n + 1) * fac n := rfl
example : fac 4 = 24 := rfl
#eval fac 100


theorem fac_pos (n : ℕ) : 0 < fac n := by {
  induction n
  case zero =>
    rw [fac]
    norm_num
  case succ k ih =>
    rw [fac]
    positivity
    -- apply mul_pos
    -- · apply?
    -- · exact ih

  -- induction n with
  -- | zero =>
  --   rw [fac]
  --   norm_num
  -- | succ n ih =>
}

/-Two useful tactics:
* `norm_num`: compute equalities and inequalities involving numerals
* `positivity`: can show that something is positive/non-negative from using that
its components are positive/non-negative.-/

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  induction n
  case zero =>
    norm_num
  case succ k ih =>
    rw [fac, pow_add, mul_comm]
    gcongr
    linarith -- or apply?
}

/-
1.2 induction when involving big operator-/

open BigOperators Finset

/- We can use `∑ i in range (n + 1), f i` to take the sum `f 0 + f 1 + ⋯ + f n`. -/
example (f : ℕ → ℝ) : ∑ i in range 0, f i = 0 :=
  sum_range_zero f
example (f : ℕ → ℝ) (n : ℕ) : ∑ i in range (n + 1), f i = (∑ i in range n, f i) + f n :=
  sum_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  induction n
  case zero => simp
  case succ k ih =>
    rw [fac, prod_range_succ, ← ih, mul_comm]
}

/- The following result is denoted using division of natural numbers.
This is defined as division, rounded down.
This makes it harder to prove things about it, so we generally avoid using it
(unless you actually want to round down sometimes).
We can just prove another formula, multiplied each side by 2.-/

theorem sum_id (n : ℕ) :
  (∑ i in range (n + 1), i) = n * (n + 1) / 2 := by {
  symm
  rw [Nat.div_eq_of_eq_mul_left]
  norm_num
  symm
  induction n
  case zero => simp
  case succ k ih =>
    rw [sum_range_succ, add_mul, ih]
    ring
}

/-
1.3 Notes for coercion

When using division, it is better to do the calculation in the rationals or reals.
Note that we write `(... : ℚ)` in the left hand side to *coerce* the value to the rationals.
In the infoview (right half of your screen), these coercions are denoted with `↑`.

Some tactics that are useful when working with coercions:
* `norm_cast`: pull coercions out of an expression.
  E.g. turn `↑n * ↑m + ↑k` into `↑(n * m + k)`
* `push_cast`: push coercions into an expression.
  E.g. turn `↑(n * m + k)` into `↑n * ↑m + ↑k`

Warning: when coercing from `ℕ` to e.g. `ℚ`
these tactics will not push/pull casts along `-` or `/`,
since `↑n - ↑m = ↑(n - m)` and `↑n / ↑m = ↑(n / m)` are not always true.
-/

#check (3 : ℚ)
variable (n : ℕ)
#check (n : ℚ)
#check (n : ℝ)

example : (∑ i in range (n + 1), i : ℚ) = n * (n + 1) / 2 := by {
  induction n
  case zero => simp
  case succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
}



/-
1.4 Fibonacci Sequence-/

/-
1.4.1 define the Fibonacci sequence and some exercises as to the simplest induction -/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

/- # Exercises -/

example : ∑ i in range n, fib (2 * i + 1) = fib (2 * n) := by {
  induction n
  case zero => simp
  case succ n ih =>
    rw [sum_range_succ,ih,mul_add,mul_one,add_comm]
    rfl
}

example : (∑ i in range n, fib i : ℤ) = fib (n + 1) - 1 := by {
  induction n
  case zero => simp
  case succ n ih =>
    rw [sum_range_succ,ih,← add_sub_right_comm,sub_left_inj]
    rfl
}

example : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  induction n
  case zero => simp
  case succ n ih =>
    rw [sum_range_succ,mul_add,ih]
    ring
}

example : (∑ i in range (n + 1), i ^ 3 : ℚ) = (n * (n + 1) / 2 : ℚ) ^ 2 := by {
  induction n
  case zero => simp
  case succ n ih =>
    rw [sum_range_succ,ih]
    push_cast
    ring
}

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  induction n
  case zero => simp
  case succ n ih =>
    rw [mul_add, mul_one,fac,fac,ih,add_assoc,← mul_two]
    rw [mul_comm 1 2,← mul_add]
    rw [← mul_assoc (2 * n + 1),mul_comm (2 * n + 1)]
    rw [mul_assoc (fac n * 2 ^ n)]
    rw [mul_comm (2 * n + 1),← prod_range_succ]
    rw [← mul_assoc (2 * (n+1)),← mul_assoc (2 * (n+1)),mul_assoc 2]
    rw [← fac_succ]
    rw [mul_comm 2,mul_assoc (fac (n+1))]
    nth_rw 1 [← pow_one 2]
    rw [← pow_add, add_comm 1 n]
}

/-
1.4.2 Two-Step Induction

Let's prove an explicit formula for the Fibonacci sequence.
Along the way, we will want to write and use some lemmas about `ϕ` and `ψ`-/

def ϕ : ℝ := (1 + sqrt 5) / 2
def ψ : ℝ := (1 - sqrt 5) / 2

/- `Nat.two_step_induction` can be used to do an induction with 2 induction hypotheses, i.e.
`P n → P (n + 1) → P (n + 2)`. -/

@[simp] lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0 := by
  simp [ϕ, ψ, sub_eq_zero]
  simp [sub_eq_add_neg]
  norm_num

@[simp] lemma ϕ_sq : ϕ ^ 2 = ϕ + 1 := by
  simp [ϕ, add_sq]
  field_simp
  ring

@[simp] lemma ψ_sq : ψ ^ 2 = ψ + 1 := by
  simp [ψ, sub_sq]
  field_simp
  ring

#check Nat.two_step_induction

lemma coe_fib_eq (n : ℕ) : (fib n : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ) := by
  induction n using Nat.two_step_induction
  case zero => simp
  case one => simp
  case step k ih1 ih2 =>
    simp [fib, ih1, ih2]
    field_simp
    simp [pow_add]
    ring

/- The following lemmas will be useful for this.
* `field_simp` is a useful tactic that can often cancel denominators. -/

/-
1.5 `Nat.strongRec` is used for strong induction-/

#check Nat.strongRec

/-
1.6 induct on other inductively defined types

`Nat.le_induction` is used to induct in equalities of the natural numbers. -/
theorem fac_dvd_fac (n m : ℕ) (h : n ≤ m) : fac n ∣ fac m := by sorry

#check Nat.le_induction


open Topology Filter

/- `TopologicalSpace.generateFrom` is the smallest topology containing
a specific collection of sets. It is defined inductively. -/
#check TopologicalSpace.generateFrom

open TopologicalSpace
theorem le_generateFrom_iff_subset_isOpen {α : Type*} {t : TopologicalSpace α}
    {g : Set (Set α)} (h : g ⊆ { s | IsOpen[t] s }) :
    { s | IsOpen[generateFrom g] s } ⊆ { s | IsOpen[t] s } := by {
  intro s hs
  simp
  simp at hs
  induction hs
  case basic s hs =>
    apply h
    exact hs
  case univ =>
    simp
  case inter s s' _ _ ihs ihs' =>
    apply IsOpen.inter
    exact ihs
    exact ihs'
  case sUnion S _ hS =>
    apply isOpen_sUnion
    exact hS
}


/- One can also state, prove and use induction principle for objects whose definition
is not inductive. -/

#check IsCompact.induction_on

#check Submodule.span_induction

#check IntermediateField.induction_on_adjoin



/- # II.A warning on casts

* (in)equalities in different types are not the same statement.

* you can use `norm_cast` to simplify (in)equalities involving casts. -/

example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by
  norm_cast at h
  rw [h]

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by
  gcongr
  norm_cast

example (n : ℤ) (h : 0 < n) : 0 < sqrt n := by
  rw [sqrt_pos]
  norm_cast

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by norm_cast

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by norm_cast




/- Warning: sometimes you have to use `clear` to get rid of hypotheses when doing induction. -/
example (hn : 2 ∣ n) :
    (∑ i in range (n + 1), i : ℚ) = n * (n + 1) / 2 := by {
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring
}
