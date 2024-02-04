import LeanCourse.Common
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Defs
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Order.Ideal
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic.ComputeDegree


open Nat.ModEq GaussianInt Zsqrtd Complex Polynomial

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 40000

/- ## Part 1 : uncomplicated lemmas in the main theorem -/


-- for any natural number x, x² ≡ 0 or 1 [MOD 4]
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


variable (p : ℕ) (h : Nat.Prime p) [Fact (Nat.Prime p)]
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



/- ## Part 2 : 𝔽ₚ[X] ⧸ (X² + 1) ≃+* ℤ[i] ⧸ (p) -/


--Explanation 2
-- # 𝔽ₚ[X] ≃+* ℤ ⧸ (p) [X]

noncomputable def Equiv1 : Polynomial (ZMod p) ≃+* Polynomial (ℤ ⧸ Ideal.span {(p : ℤ)}) :=
  Polynomial.mapEquiv (RingEquiv.symm (Int.quotientSpanNatEquivZMod p))

/-
lemma Equiv2 : Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)} ≃+*
  Polynomial (ℤ ⧸ Ideal.span {(p : ℤ)}) ⧸
  Ideal.span {monomial 2 (1 : ℤ ⧸ Ideal.span {(p : ℤ)}) + C (1 : ℤ ⧸ Ideal.span {(p : ℤ)})} := by sorry
-/

-- 𝔽ₚ[X] ⧸ (X² + 1) ≃+* (ℤ ⧸ (p) [X]) / (X² + 1)
lemma IsImage1 :
  map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1) =
  (Equiv1 p) (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) := by
  rw [Equiv1]
  simp
  congr
  symm
  simp

lemma IdealEq1 : Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)} =
  Ideal.map (Equiv1 p) (Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)}) := by
  rw [Ideal.map_span, Set.image_singleton, IsImage1 p]

lemma Equiv2 : Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)} ≃+*
  Polynomial (ℤ ⧸ Ideal.span {(p : ℤ)}) ⧸
  Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)} :=
  Ideal.quotientEquiv (Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)})
    (Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)})
    (Equiv1 p) (IdealEq1 p)



-- # ℤ[i] ⧸ (p) ≃+* ℤ ⧸ (p) [X] ⧸ (X² + 1)

-- first, we prove "as ℤ-algebra, ℤ[i] has a basis {1, i}"
def BasisFun (x : Fin 2) : ℤ[i] :=
  if (x = 0) then 1 else { re := 0, im := 1}

lemma LI : LinearIndependent ℤ BasisFun := by
{
  apply Fintype.linearIndependent_iff.2
  intro g hg
  simp at hg
  have hsum: ({ re := (g 0), im := (g 1)} : ℤ[i]) = 0 :=
    calc ({ re := (g 0), im := (g 1)} : ℤ[i])
      = (g 0) * { re := 1, im := 0} + (g 1) * { re := 0, im := 1} := by simp
     _= (g 0) * 1 + (g 1) * { re := 0, im := 1} := rfl
     _= (g 0) * BasisFun 0 + (g 1) * BasisFun 1 := rfl
     _= 0 := hg
  rw [Fin.forall_fin_two]
  constructor
  · calc g 0 = ({ re := g 0, im := g 1} : ℤ[i]).re := rfl
      _= (0 : ℤ[i]).re := by rw [hsum]
      _= 0 := rfl
  · calc g 1 = ({ re := g 0, im := g 1} : ℤ[i]).im := rfl
      _= (0 : ℤ[i]).im := by rw [hsum]
      _= 0 := rfl
}

lemma SP : ⊤ ≤ Submodule.span ℤ (Set.range BasisFun) := by
{
  apply (top_le_span_range_iff_forall_exists_fun ℤ).2
  intro x
  simp
  let c := fun (i : Fin 2) ↦ if (i = 0) then x.re else x.im
  use c
  calc (c 0) * BasisFun 0 + (c 1) * BasisFun 1
    = (c 0) * { re := 1, im := 0} + (c 1) * { re := 0, im := 1} := rfl
   _= x.re * { re := 1, im := 0} + (c 1) * { re := 0, im := 1} := rfl
   _= { re := x.re, im := x.im} := by simp
   _= x := rfl
}

noncomputable def PB : PowerBasis ℤ ℤ[i] where
  gen := { re := 0, im := 1}
  dim := 2
  basis := Basis.mk LI SP
  basis_eq_pow := by simp


-- now we can use 'PowerBasis.quotientEquivQuotientMinpolyMap'
lemma Equiv3 : (ℤ[i] ⧸ Ideal.map (algebraMap ℤ ℤ[i]) (Ideal.span {(p : ℤ)})) ≃+*
  Polynomial (ℤ ⧸ (Ideal.span {(p : ℤ)})) ⧸
    Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (minpoly ℤ PB.gen)} :=
  PowerBasis.quotientEquivQuotientMinpolyMap PB (Ideal.span {(p : ℤ)})


-- ℤ[i] ⧸ (p) ≃+* the left hand side of Equiv3
lemma IdealEq2 : Ideal.span {(p : ℤ[i])} =
  Ideal.map (algebraMap ℤ ℤ[i]) (Ideal.span {(p : ℤ)}) := by
  rw [Ideal.map_span, Set.image_singleton]
  simp

lemma Equiv4 : ℤ[i] ⧸ Ideal.span {(p : ℤ[i])} ≃+*
  (ℤ[i] ⧸ Ideal.map (algebraMap ℤ ℤ[i]) (Ideal.span {(p : ℤ)})) :=
  Ideal.quotEquivOfEq (IdealEq2 p)


-- the ring hand side of Equiv3 ≃+* ℤ ⧸ (p) [X] ⧸ (X² + 1)

--lemma GaussianInt_IsIntegral : IsIntegral ℤ ℤ[i] := by sorry

lemma MinPoly : minpoly ℤ PB.gen = monomial 2 (1 : ℤ) + C 1 := by
{
  rw [minpoly]
  sorry
}

lemma Equiv5 : Polynomial (ℤ ⧸ (Ideal.span {(p : ℤ)})) ⧸
  Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (minpoly ℤ PB.gen)} ≃+*
  Polynomial (ℤ ⧸ Ideal.span {(p : ℤ)}) ⧸
  Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)} := by rw [MinPoly]


-- # Fₚ[X] ⧸ (X² + 1) ≃+* ℤ[i] ⧸ (p)
theorem KeyEquiv  :
  Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)} ≃+*
   ℤ[i] ⧸ Ideal.span {(p : ℤ[i])} :=
   (Equiv2 p).trans ((Equiv4 p).trans ((Equiv3 p).trans (Equiv5 p))).symm



/- ## Part 3 : 𝔽ₚ[X] / (X² + 1) is not a field -/


lemma UnitsIsCyclic : IsCyclic (ZMod p)ˣ := by infer_instance


lemma lt_five (x : ℕ) (h : x - 1 < 4) : x < 5 := lt_of_tsub_lt_tsub_right h


-- p is prime and p ≡ 1 [MOD 4] => 'p < 5' should not hold
lemma Not_pltfive (hmod : p ≡ 1 [MOD 4]) : ¬ p < 5 := by
  by_contra hlt
  interval_cases p
  · exact Nat.not_prime_zero h
  · exact Nat.not_prime_one h
  · simp at hmod
  · simp at hmod
  · simp at hmod



-- when the prime satisfies p ≡ 1 [MOD 4], 𝔽ₚ[X]/(X² + 1) isn't a field
theorem IsNotField (hmod : p ≡ 1 [MOD 4]) :
  ¬ IsField (Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)}) := by {
  -- 𝔽ₚˣ is a cyclic group, let ξ be the generator
  -- 'exists_generator' is a built_in property of Class 'IsCyclic'
  obtain ⟨ξ,hξ⟩ := (UnitsIsCyclic p).exists_generator


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

  -- from hp2 to hp4, we prove 'ξ ^ (2 * n) = -1' via '(ξ ^ (2 * n)) ^ 2 = 1' but 'ξ ^ (2 * n) ≠ 1'
  have hp2 : ((ξ : ZMod p) ^ (2 * n)) ^ 2 = 1 := by
    calc ((ξ : ZMod p) ^ (2 * n)) ^ 2
       = (ξ : ZMod p) ^ ((2 * n) * 2) := by rw [← pow_mul]
      _= (ξ : ZMod p) ^ (4 * n) := by rw [mul_comm, ← mul_assoc]
      _= 1 := by norm_cast; rw [hp1]; norm_cast
  rw [sq_eq_one_iff, or_comm, or_iff_not_imp_left] at hp2

  -- we prove 'ξ ^ (2 * n) ≠ 1' via '2 * n < OrderOf ξ'
  have hp3 : ξ ^ (2 * n) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf'
      · simp
        by_contra nhp
        rw [Nat.div_eq_zero_iff four_pos] at nhp
        apply lt_five at nhp
        exact Not_pltfive p h hmod nhp

      · -- we prove 'OrderOf ξ = p - 1' via '|𝔽ₚˣ| = |𝔽ₚ| - 1'
        have CardOfUnits : Fintype.card (ZMod p) = Fintype.card (ZMod p)ˣ + 1 := by
          rw [Fintype.card_eq_card_units_add_one]
        rw [ZMod.card p] at CardOfUnits
        apply Nat.sub_eq_of_eq_add at CardOfUnits
        symm at CardOfUnits
        rw [← orderOf_eq_card_of_forall_mem_zpowers hξ] at CardOfUnits

        rw [CardOfUnits]
        simp
        -- our goal can be simplified to '2 * ((p - 1) / 4) < p - 1'

        have hlt : 2 * (p - 1) / 4 < p - 1 := by
          rw [Nat.div_lt_iff_lt_mul', mul_comm (p - 1)]
          apply Nat.mul_lt_mul_of_pos_right
          linarith
          simp
          exact Nat.Prime.one_lt h
          linarith

        calc 2 * ((p - 1) / 4)
           ≤ 2 * (p - 1) / 4 := Nat.mul_div_le_mul_div_assoc 2 (p - 1) 4
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
  have mul_mem :
    (monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n)) * (monomial 1 (1 : (ZMod p)) + C ((ξ : ZMod p) ^ n)) =
    monomial 2 (1 : ZMod p) + C (1 : ZMod p) := by ring; simp; ring; rw [mul_comm, ← RingHom.map_pow, hp4] ; simp

  have self_mem : (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) ∈ (Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)}) :=
    Ideal.mem_span_singleton_self (monomial 2 (1 : ZMod p) + C (1 : ZMod p))
  nth_rewrite 1 [← mul_mem] at self_mem


  -- in addition, 'X - ξ ^ n , X + ξ ^ n ∉ (X² + 1)' via analysing polynomial degree
  specialize hfield self_mem
  obtain hl|hr := hfield


  · rw [Ideal.mem_span_singleton] at hl
    have hl0 : natDegree ((monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n))) = 1 := by compute_degree; norm_num
    have hl1 : (monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n)) ≠ 0 := by
      by_contra hpp
      rw [hpp] at hl0
      simp at hl0

    apply (Polynomial.degree_le_of_dvd hl) at hl1
    have hl2 : degree (monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n)) < degree (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) :=
      calc degree (monomial 1 (1 : (ZMod p)) + C (- (ξ : ZMod p) ^ n))
        = 1 := by compute_degree; norm_num
       _< 2 := by simp
       _= degree (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) := by symm; compute_degree; norm_num
    apply lt_iff_not_le.1 at hl2
    contradiction

  · rw [Ideal.mem_span_singleton] at hr
    have hr0 : natDegree ((monomial 1 (1 : (ZMod p)) + C ((ξ : ZMod p) ^ n))) = 1 := by compute_degree; norm_num
    have hr1 : (monomial 1 (1 : (ZMod p)) + C ((ξ : ZMod p) ^ n)) ≠ 0 := by
      by_contra hpp
      rw [hpp] at hr0
      simp at hr0

    apply (Polynomial.degree_le_of_dvd hr) at hr1
    have hr3 : degree (monomial 1 (1 : (ZMod p)) + C ((ξ : ZMod p) ^ n)) < degree (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) :=
      calc degree (monomial 1 (1 : (ZMod p)) + C ((ξ : ZMod p) ^ n))
        = 1 := by compute_degree; simp
       _< 2 := by simp
       _= degree (monomial 2 (1 : ZMod p) + C (1 : ZMod p)) := by symm; compute_degree; norm_num
    apply lt_iff_not_le.1 at hr3
    contradiction
}



/- ## Part 4 : Fermat's Theorem on sums of two squares -/


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




/-
-- (ℤ ⧸ (p) [X]) / (X² + 1) ≃+* (ℤ[X] ⧸ (p)) ⧸ (X² + 1)

noncomputable def Equiv3 : Polynomial (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃+* Polynomial ℤ ⧸ Ideal.map C (Ideal.span {(p : ℤ)}) :=
  Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {(p : ℤ)})

lemma IsImage1 :
  Ideal.map (Ideal.Quotient.mk (Ideal.map C (Ideal.span {(p : ℤ)}))) (Ideal.span {monomial 2 (1 : ℤ) + C 1}) =
  Ideal.map (Equiv3 p) (Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)}) := by
  rw [Ideal.map_span (Ideal.Quotient.mk (Ideal.map C (Ideal.span {(p : ℤ)}))),
      Ideal.map_span (Equiv3 p)]
  rw [Set.image_singleton , Set.image_singleton , Equiv3]
  rw [Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk (Ideal.span {(p : ℤ)}) (monomial 2 (1 : ℤ) + C 1)]

lemma Equiv4 : Polynomial (ℤ ⧸ Ideal.span {(p : ℤ)}) ⧸
  Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)} ≃+*
  (Polynomial ℤ ⧸ Ideal.map C (Ideal.span {(p : ℤ)})) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.map C (Ideal.span {(p : ℤ)}))) (Ideal.span {monomial 2 (1 : ℤ) + C 1}) :=
  Ideal.quotientEquiv (Ideal.span {map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) (monomial 2 (1 : ℤ) + C 1)})
  (Ideal.map (Ideal.Quotient.mk (Ideal.map C (Ideal.span {(p : ℤ)}))) (Ideal.span {monomial 2 (1 : ℤ) + C 1}))
  (Equiv3 p) (IsImage1 p)


-- 𝔽ₚ[X] ⧸ (X² + 1) ≃+* (ℤ[X] ⧸ (p)) ⧸ (X² + 1)
lemma Equiv6 : Polynomial (ZMod p) ⧸ Ideal.span {monomial 2 (1 : ZMod p) + C (1 : ZMod p)} ≃+*
  (Polynomial ℤ ⧸ Ideal.span {C (p : ℤ)}) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {C (p : ℤ)})) (Ideal.span {monomial 2 (1 : ℤ) + C 1}) :=
  (Equiv2 p).trans (Equiv3 p)
-/



/-
-- (ℤ[X] ⧸ (p)) ⧸ (X² + 1) ≃+* (ℤ[X] ⧸ (X² + 1)) ⧸ (p)
lemma Equiv4 : (Polynomial ℤ ⧸ Ideal.span {C (p : ℤ)}) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {C (p : ℤ)})) (Ideal.span {monomial 2 (1 : ℤ) + C 1}) ≃+*
  (Polynomial ℤ ⧸ Ideal.span {monomial 2 (1 : ℤ) + C 1}) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {monomial 2 (1 : ℤ) + C 1})) (Ideal.span {C (p : ℤ)}) :=
  DoubleQuot.quotQuotEquivComm (Ideal.span {C (p : ℤ)}) (Ideal.span {monomial 2 (1 : ℤ) + C 1})


-- (ℤ[X] ⧸ (X² + 1)) ⧸ (p) ≃+* ℤ[i] ⧸ (p)
lemma Equiv5 : (Polynomial ℤ ⧸ Ideal.span {monomial 2 (1 : ℤ) + C 1}) ≃+* ℤ[i] := by sorry

lemma IsImage2 : Ideal.span {(p : ℤ[i])} =
  Ideal.map (Equiv5 : (Polynomial ℤ ⧸ Ideal.span {monomial 2 (1 : ℤ) + C 1}) →+* ℤ[i])
  (Ideal.map (Ideal.Quotient.mk (Ideal.span {monomial 2 (1 : ℤ) + C 1})) (Ideal.span {C (p : ℤ)})) := by
  ext x
  constructor
  · intro hx
    sorry
  sorry

lemma Equiv6 : (Polynomial ℤ ⧸ Ideal.span {monomial 2 (1 : ℤ) + C 1}) ⧸
  Ideal.map (Ideal.Quotient.mk (Ideal.span {monomial 2 (1 : ℤ) + C 1})) (Ideal.span {C (p : ℤ)}) ≃+*
  ℤ[i] ⧸ Ideal.span {(p : ℤ[i])} :=
  Ideal.quotientEquiv (Ideal.map (Ideal.Quotient.mk (Ideal.span {monomial 2 (1 : ℤ) + C 1})) (Ideal.span {C (p : ℤ)}))
    (Ideal.span {(p : ℤ[i])}) Equiv5 (IsImage2 p)
-/
