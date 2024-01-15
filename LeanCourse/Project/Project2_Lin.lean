import LeanCourse.Common
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Defs
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Order.Ideal
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Nat.Order.Lemmas


open Nat.ModEq GaussianInt Zsqrtd Complex Polynomial


/- # Part 1 : uncomplicated lemmas in the main theorem -/


-- for any integer x, x² ≡ 0 or 1 [MOD 4]
lemma Square_mod_four {x : ℕ} (h : ¬ x ^ 2 ≡ 0 [MOD 4]): x ^ 2 ≡ 1 [MOD 4] := by
{
  mod_cases hp : (x : ℤ) % 4
  · apply Int.coe_nat_modEq_iff.1 at hp
    apply (Nat.ModEq.mul_left x) at hp
    rw [← pow_two] at hp
    contradiction
  · apply Int.coe_nat_modEq_iff.1 at hp
    apply (Nat.ModEq.mul hp) at hp
    rw [← pow_two] at hp
    exact hp
  · apply Int.coe_nat_modEq_iff.1 at hp
    apply (Nat.ModEq.mul hp) at hp
    rw [← pow_two] at hp
    contradiction
  · apply Int.coe_nat_modEq_iff.1 at hp
    apply (Nat.ModEq.mul hp) at hp
    rw [← pow_two] at hp
    exact hp
}


-- k ∈ ℕ , k ≤ 2 iff k = 0, 1 or 2
lemma le_two_iff (k : ℕ) : k ≤ 2 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by {
  constructor
  · intro hk
    interval_cases k
    tauto
    tauto
    tauto
  · intro h
    obtain h1|h2|h3 := h
    linarith
    linarith
    linarith
}


variable (p : ℕ) (h : Nat.Prime p)
local notation "ℤ[i]" => GaussianInt


-- p is prime => p² ≠ 0
lemma psquare_notzero : p ^ 2 ≠ 0 := by
{
  by_contra hp
  rw [pow_eq_zero_iff] at hp
  subst p
  apply Nat.not_prime_zero at h
  assumption
  norm_num
}


-- following two lemmas prove p isn't a unit in ℤ[i]
lemma p2_IsPrimePow : IsPrimePow ((p : ℤ) * p) := by {
  rw [isPrimePow_def]
  use p, 2
  constructor
  · exact Nat.prime_iff_prime_int.mp h
  constructor
  linarith
  exact sq (p : ℤ)
}

-- here we use 'x ∈ ℤ[i] is a unit iff ‖x‖ ∈ ℤ is a unit"
-- but ‖p‖ = p² cannot be a unit since it is a prime power
lemma Isnotunit : ¬ IsUnit (p : ℤ[i]) := by
{
  by_contra nh
  rw [Zsqrtd.isUnit_iff_norm_isUnit] at nh
  rw [Zsqrtd.norm_nat_cast] at nh
  apply p2_IsPrimePow at h
  apply IsPrimePow.not_unit at h
  contradiction
}


lemma negone_le_zero : -1 ≤ 0 := by simp



/- # Part 2 : 𝔽ₚ[X] ⧸ (X² + 1) ≃+* ℤ[i] ⧸ (p) -/


def tof_1 (x : (ZMod p)) : ℤ[i] ⧸ Ideal.span {(p : ℤ[i])} := x.val

def tof_1' : RingHom (ZMod p) (ℤ[i] ⧸ Ideal.span {(p : ℤ[i])}) where
  toFun := (tof_1 p)
  map_one' := by {
    rw [tof_1]
    have hp : ZMod.val (1 : ZMod p) = 1 := by
      sorry
    rw [hp]
    norm_cast
  }
  map_mul' := by intro x y; simp; rw [tof_1,tof_1,tof_1]; norm_cast; sorry
  map_zero' := by simp; rw [tof_1]; simp
  map_add' := by intro x y; simp; rw [tof_1,tof_1,tof_1]; norm_cast;sorry

--def tof_2 : Polynomial (ZMod p) → (ℤ[i] ⧸ Ideal.span {(p : ℤ[i])}) :=
  --Polynomial.eval₂ (tof_1' p) (I : (ℤ[i] ⧸ Ideal.span {(p : ℤ[i])}))



def KeyEquivClass : RingEquiv
  (Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)})
  (ℤ[i] ⧸ Ideal.span {(p : ℤ[i])}) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry



theorem KeyEquiv  :
  Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)} ≃+*
   ℤ[i] ⧸ Ideal.span {(p : ℤ[i])} := by {
  sorry
}



/- # Part 3 : 𝔽ₚ[X] / (X² + 1) is not a field -/


-- we need to apply '𝔽ₚ is a domain' again and again
lemma FpIsDomain : IsDomain (ZMod p) := by
  apply fact_iff.2 at h
  exact ZMod.instIsDomainZModToSemiringToDivisionSemiringToSemifieldInstFieldZMod p


lemma UnitsIsCyclic : IsCyclic (ZMod p)ˣ := by
  -- 𝔽ₚ is a domain
  have : IsDomain (ZMod p) := FpIsDomain p h

  -- 𝔽ₚˣ is finite
  -- here is some unbearable trouble
  -- the final theorem require '𝔽ₚˣ is Finite' but in Mathlib, I can only find '𝔽ₚ is Fintype'
  -- thus I need to provide some trivial conversion between 'Finite' and 'Fintype
  have : NeZero p := by rw [neZero_iff]; exact Nat.Prime.ne_zero h
  have : Finite (ZMod p) := by
    apply Fintype.finite
    apply ZMod.fintype p
  have : Finite (ZMod p)ˣ := instFiniteUnits

  -- as to a domain, its Units is a cyclic group w.r.t. multiplication if Units is finite
  exact instIsCyclicUnitsToMonoidToMonoidWithZeroToSemiringToCommSemiringInstGroupUnits


-- 𝔽ₚ does not have nonzero zero divisor since it is a domain
lemma FpNoZeroDivisor : NoZeroDivisors (ZMod p) := by
  have hp : IsDomain (ZMod p) := FpIsDomain p h
  refine IsDomain.to_noZeroDivisors (ZMod p)


lemma lt_five (x : ℕ) (h : x - 1 < 4) : x < 5 := by exact lt_of_tsub_lt_tsub_right h


lemma not_primeltfive (hmod : p ≡ 1 [MOD 4]) : ¬ p < 5 := by
  by_contra hlt
  interval_cases p
  · exact Nat.not_prime_zero h
  · exact Nat.not_prime_one h
  · simp at hmod
  · simp at hmod
  · simp at hmod


lemma Fp_mul_inv_cancel : ∀ (a : ZMod p), a ≠ 0 → a * a⁻¹ = 1 := by
  intro a ha
  rw [ZMod.mul_inv_eq_gcd]
  sorry

instance : GroupWithZero (ZMod p) where
  exists_pair_ne := by
    rw [← _root_.nontrivial_iff]
    have : Fact (1 < p) := fact_iff.2 (Nat.Prime.one_lt h)
    exact ZMod.nontrivial p
  inv_zero := ZMod.inv_zero p
  mul_inv_cancel := Fp_mul_inv_cancel p



-- when the prime satisfies p ≡ 1 [MOD 4], 𝔽ₚ[X]/(X² + 1) isn't a field
theorem IsNotField (hmod : p ≡ 1 [MOD 4]) :
  ¬ IsField (Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)}) := by {
  -- 𝔽ₚˣ is a cyclic group, let ξ be the generator
  -- 'exists_generator' is a built_in property of Class 'IsCyclic'
  obtain ⟨ξ,hξ⟩ := (UnitsIsCyclic p h).exists_generator


  let n := (p - 1) / 4

  -- from 'hp1' to 'hp4', we prove 'ξ ^ (4 * n) = 1' and 'ξ ^ (2 * n) = -1'
  have hp1 : ξ ^ (4 * n) = 1 := by
    simp
    rw [Nat.mul_div_cancel_left']
    apply fact_iff.2 at h
    refine ZMod.units_pow_card_sub_one_eq_one p ξ
    refine (Nat.modEq_iff_dvd' ?h).mp (id (Nat.ModEq.symm hmod))
    apply le_of_lt
    exact Nat.Prime.one_lt h

  -- prove 'ξ ^ (2 * n) = -1' via '(ξ ^ (2 * n)) ^ 2 = 1' but 'ξ ^ (2 * n) ≠ 1'
  have hp2 : ((ξ : ZMod p) ^ (2 * n)) ^ 2 = 1 := by
    calc ((ξ : ZMod p) ^ (2 * n)) ^ 2
       = (ξ : ZMod p) ^ ((2 * n) * 2) := by rw [← pow_mul]
      _= (ξ : ZMod p) ^ (4 * n) := by rw [mul_comm, ← mul_assoc]
      _= 1 := by norm_cast; rw [hp1]; norm_cast

  let hpp := FpNoZeroDivisor p h
  rw [sq_eq_one_iff, or_comm, or_iff_not_imp_left] at hp2

  have hp3 : ξ ^ (2 * n) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf'
      · simp
        by_contra nhp'
        rw [Nat.div_eq_zero_iff four_pos] at nhp'
        apply lt_five at nhp'
        exact not_primeltfive p h hmod nhp'
      · have NeZerop : NeZero p := by rw [neZero_iff]; exact Nat.Prime.ne_zero h
        have FpIsFinType : Fintype (ZMod p) := by exact ZMod.fintype p
        have FpGroupwithUnits : GroupWithZero (ZMod p) := by exact instGroupWithZeroZMod p h
        have CardOfUnits : Fintype.card (ZMod p) = Fintype.card (ZMod p)ˣ + 1 := by
          rw [Fintype.card_eq_card_units_add_one]
          sorry
        rw [ZMod.card p] at CardOfUnits
        apply Nat.sub_eq_of_eq_add at CardOfUnits
        symm at CardOfUnits
        rw [← orderOf_eq_card_of_forall_mem_zpowers hξ] at CardOfUnits
        rw [CardOfUnits]
        simp
        have hlt : 2 * (p - 1) / 4 < p - 1 := by
          rw [Nat.div_lt_iff_lt_mul', mul_comm (p - 1)]
          apply Nat.mul_lt_mul_of_pos_right
          linarith
          simp
          exact Nat.Prime.one_lt h
          linarith
        calc 2 * ((p - 1) / 4) ≤ 2 * (p - 1) / 4 := Nat.mul_div_le_mul_div_assoc 2 (p - 1) 4
          _< p - 1 := hlt

  have hp4 : (ξ : ZMod p) ^ (2 * n) = -1 := by
    by_contra nhp
    apply hp2 at nhp
    have hp4' : ξ ^ (2 * n) = 1 := by norm_cast at nhp; exact Units.val_eq_one.mp nhp
    contradiction


  -- 𝔽ₚ[X]/(X² + 1) is a field => (X² + 1) is a max ideal, thus a prime ideal
  -- as a consequence, x * y ∈ (X² + 1) => 'x ∈ (X² + 1)' or 'y ∈ (X² + 1)
  by_contra hfield
  apply Ideal.Quotient.maximal_of_isField at hfield
  apply Ideal.IsMaximal.isPrime at hfield
  apply Ideal.IsPrime.mem_or_mem at hfield

  -- but we have (X - ξ ^ n) * (X + ξ ^ n) = X² + 1
  have mul_mem : (monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n)) * (monomial 1 (1 : (ZMod p)) + C (ξ : ZMod p) ^ n) =
    monomial 2 (1 : ZMod p) + C (1 : ZMod p) := by
    calc (monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n)) * (monomial 1 (1 : (ZMod p)) + C (ξ : ZMod p) ^ n)
       = (monomial 1 (1 : (ZMod p))) * (monomial 1 (1 : (ZMod p))) + C (- (ξ : ZMod p) ^ n) * C (ξ : ZMod p) ^ n
         := by sorry
      _=  monomial 2 (1 : ZMod p) + C (1 : ZMod p) := by sorry

  have self_mem : (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) ∈ (Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)}) :=
    Ideal.mem_span_singleton_self (monomial 2 (1 : ZMod p) + C (1 : ZMod p))
  nth_rewrite 1 [← mul_mem] at self_mem

  -- but X - ξ ^ n , X + ξ ^ n ∉ (X² + 1) via analysing polynomial degree
  specialize hfield self_mem
  obtain hl|hr := hfield
  · sorry
  · sorry
}



/- # Part 4 : Fermat's Theorem on sums of two squares -/


theorem Fermat_on_sums_of_two_squares :
  (∃ x y : ℕ , p = x ^ 2 + y ^ 2) ↔ p = 2 ∨ p ≡ 1 [MOD 4] := by
{
  constructor
  · -- to prove "p = x² + y² for some integers x y => p = 2 or p ≡ 1 [MOD 4]"
    intro ⟨x, y, hxy⟩
    -- to prove via "for any integer x, x² ≡ 0 or 1 [MOD 4]", this induces four cases
    by_cases hx : x ^ 2 ≡ 0 [MOD 4]
    · by_cases hy : y ^ 2 ≡ 0 [MOD 4]
      · have hp : 4 ∣ p := by
          apply Nat.modEq_zero_iff_dvd.1
          rw [hxy, ← add_zero 0]
          apply Nat.ModEq.add hx hy
        rw [Nat.dvd_prime h] at hp
        simp at hp
        clear hxy -- if not clear hxy, tactic "subst" will use hxy rather than hp
        subst p
        simp at h
        -- result : contradiction
      · right
        apply Square_mod_four at hy
        rw [← add_zero 1, add_comm]
        subst p
        apply Nat.ModEq.add hx hy
    · by_cases hy : y ^ 2 ≡ 0 [MOD 4]
      · right
        apply Square_mod_four at hx
        rw [← add_zero 1]
        subst p
        apply Nat.ModEq.add hx hy
      · left
        apply Square_mod_four at hx
        apply Square_mod_four at hy
        apply Nat.ModEq.add at hx
        apply hx at hy
        rw [← hxy, one_add_one_eq_two] at hy
        have heven : 2 ∣ p := by
          rw [Nat.ModEq.dvd_iff hy]
          simp
        rw [← even_iff_two_dvd, Nat.Prime.even_iff h] at heven
        assumption

  · -- to prove "p = 2 or p ≡ 1 [MOD 4] => p can be written as a sum of two squares"
    intro hdisj
    obtain h1|h2 := hdisj
    · -- "p = 2" is a easy case, just use p = 1² + 1²
      use 1, 1
      simp [one_add_one_eq_two]
      assumption
    · /- at the case "p ≡ 1 [MOD 4]", we set "p ∈ ℤ[i]"
         and consider the maximal ideal m containing p
         since ℤ[i] is a PID, m = (π) for some π = x + yi
         then we try to prove "p = x² + y²" -/



      -- to find a max ideal 'm' in ℤ[i] containing 'p' via the existence of max ideals
      have hmax : ∃ (m : Ideal ℤ[i]), Ideal.IsMaximal m ∧ Ideal.span {(p : ℤ[i])} ≤ m := by
        apply  Ideal.exists_le_maximal
        apply Ideal.span_singleton_ne_top
        exact Isnotunit p h
      obtain ⟨m, ⟨hmax,hmem⟩⟩ := hmax
      rw [Ideal.span_singleton_le_iff_mem] at hmem


      -- since ℤ[i] is a PID, ∃ π ∈ ℤ[i] s.t. m = (π)
      have hPID : IsPrincipalIdealRing ℤ[i] := by
        apply EuclideanDomain.to_principal_ideal_domain
      rw [isPrincipalIdealRing_iff] at hPID
      specialize hPID m
      let π : ℤ[i] := Submodule.IsPrincipal.generator m
      have mrepr : m = Ideal.span {π} := by
        symm
        exact Submodule.IsPrincipal.span_singleton_generator m


      -- we claim that 'p = π.re² + π.im²
      let x := π.re.natAbs
      let y := π.im.natAbs
      use x, y


      -- we obtain 'π ∣ p', i.e. p = π * v for some v ∈ ℤ[]
      rw [mrepr] at hmem
      apply Ideal.mem_span_singleton'.1 at hmem
      obtain ⟨v, prepr⟩ := hmem


      -- we derive '‖π‖ ∣ p²' where ‖·‖ : ℤ[i] → ℤ , x + yi ↦ x² + y²
      have hmul : Zsqrtd.norm v * Zsqrtd.norm π = (p : ℤ) ^ 2 := by
        calc Zsqrtd.norm v * Zsqrtd.norm π = Zsqrtd.norm (v * π) := by rw [← Zsqrtd.norm_mul]
          _=  Zsqrtd.norm p := congrArg Zsqrtd.norm prepr
          _= (p : ℤ) * p := by rw [Zsqrtd.norm] ; simp
          _= (p : ℤ) ^ 2 := by rw [pow_two]

      -- Explanation 1
      -- to derive '‖π‖ = pⁱ for some i ≤ 2'
      apply congrArg Abs.abs at hmul
      nth_rewrite 1 [abs_mul] at hmul
      rw [Int.abs_eq_natAbs,Int.abs_eq_natAbs,Int.abs_eq_natAbs] at hmul
      norm_cast at hmul
      symm at hmul
      have hdvd : Int.natAbs (Zsqrtd.norm π) ∣ p ^ 2 := by
        apply dvd_iff_exists_eq_mul_left.2
        use Int.natAbs (Zsqrtd.norm v)

      apply (Nat.dvd_prime_pow h).1 at hdvd
      obtain ⟨k,⟨hk,hg⟩⟩ := hdvd


      -- separate 'k ≤ 2' into three single cases, then we can study by cases
      apply (le_two_iff k).1 at hk
      obtain hk0|hk2|hk2 := hk


      · -- when ‖π‖ = p⁰ = 1 , π is a unit, which leads to a contradiction as (π) is a max ideal
        subst k
        rw [pow_zero] at hg
        apply Zsqrtd.norm_eq_one_iff.1 at hg
        apply isUnit_iff_exists_inv.1 at hg
        obtain ⟨b, hb⟩ := hg
        have one_mem_m : 1 ∈ m := by
          apply (Submodule.IsPrincipal.mem_iff_eq_smul_generator m).2
          use b
          symm at hb
          rw [mul_comm] at hb
          exact hb
        apply Ideal.isMaximal_iff.1 at hmax
        obtain ⟨one_not_mem_m, _⟩ := hmax
        contradiction


      · -- when ‖π‖ = p¹, we can obtain what we want
        subst k
        rw [pow_one] at hg
        -- because the calculation involves the expansion of 'Zsqrtd.norm π'
        -- I suggested it can be easier to deriva an integer conclusion first
        have hg_Int : (p : ℤ) = (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by
          calc (p : ℤ) = (Int.natAbs (Zsqrtd.norm π) : ℤ) := by rw [← hg]
            _= |Zsqrtd.norm π| := by rw [← Int.abs_eq_natAbs]
            _= Zsqrtd.norm π := by rw [_root_.abs_of_nonneg (Zsqrtd.norm_nonneg negone_le_zero π)]
            _= π.re ^ 2 + π.im ^ 2 := by rw [Zsqrtd.norm, ← pow_two, mul_assoc, ← pow_two,←  neg_eq_neg_one_mul, sub_neg_eq_add]
            _= (x : ℤ) ^ 2 + (y : ℤ) ^ 2 := by rw [← Int.natAbs_sq, ← Int.natAbs_sq π.im]
        norm_cast at hg_Int


      · -- when ‖π‖ = p², we can prove (π) = (p), which would lead to a contradiction
        subst k

        -- recall v * π = ↑p , ‖π‖ = p² implies v is a unit
        rw [hg] at hmul
        symm at hmul
        nth_rewrite 2 [← one_mul (p ^ 2)] at hmul
        apply (mul_left_inj' (psquare_notzero p h)).1 at hmul
        apply Zsqrtd.norm_eq_one_iff.1 at hmul

        -- since v is a unit, (p) = (π)
        let mp := Ideal.span {(p : ℤ[i])}
        have m_eq_mp : mp = m := by
          calc mp = Ideal.span {(p : ℤ[i])} := by simp
            _= Ideal.span {v * π} := by rw [← prepr]
            _= Ideal.span {π} := by rw [Ideal.span_singleton_mul_left_unit hmul]
            _= m := by rw [← mrepr]

        -- since (π) is a max ideal, ℤ[i]/(p) is a field
        have ZiQuotIsField : IsField (ℤ[i] ⧸ mp) := by
          rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient]
          rw [m_eq_mp]
          assumption

        -- since ℤ[i]/(p) ≃+* 𝔽ₚ[X]/(X² + 1) and 𝔽ₚ[X]/(X² + 1) is not a field, we see the contradiction
        let FppQuot := Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)}
        have FppQuotIsField : IsField FppQuot := by
          apply MulEquiv.isField (ℤ[i] ⧸ mp) ZiQuotIsField
          exact RingEquiv.toMulEquiv (KeyEquiv p)
        apply (IsNotField p h h2) at FppQuotIsField

        contradiction
}
