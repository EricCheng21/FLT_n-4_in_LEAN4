import Mathlib.NumberTheory.FLT.Four

/-!
# A small project around Fermat's Last Theorem for "n = 4"

Mathlib already contains the hard proof in Mathlib.NumberTheory.FLT.Four.
This file keeps the project close to that proof, but exposes only the main
objects and a few short wrapper theorems.

The central auxiliary equation in mathlib is
a ^ 4 + b ^ 4 = c ^ 2.
-/

/-- The elementary identity behind Euclid's parametrisation of Pythagorean triples. -/
theorem pythagorean_identity (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  ring

/-- Euclid's formula, using mathlib's PythagoreanTriple definition. -/
theorem euclid_formula (m n : ℤ) :
    PythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) := by
  delta PythagoreanTriple
  rw [sq]
  ring

/--
def Fermat42 (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2
-/
theorem fermat42_eq_square {a b c : ℤ} (h : Fermat42 a b c) :
    a ^ 4 + b ^ 4 = c ^ 2 := by
  exact h.2.2

/-
## part1. The descent equation as an algebraic object

The full exponent-4 statement is reduced to the equation
a ^ 4 + b ^ 4 = c ^ 2.

Mathlib calls this package `Fermat42 a b c`; it also stores the hypotheses
a ≠ 0 and b ≠ 0. In abstract-algebra language, this is the solution set of
a homogeneous Diophantine equation. The first useful facts are its symmetries
and normal forms.
-/

/-- Unfolding Fermat42: two nonzero fourth powers adding to a square. -/
theorem fermat42_defn (a b c : ℤ) :
    Fermat42 a b c ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2 := by
  rfl

/-- The equation is symmetric in a and b. -/
theorem fermat42_swap (a b c : ℤ) :
    Fermat42 a b c ↔ Fermat42 b a c := by
  exact Fermat42.comm

/--
The equation is homogeneous. Scaling a and b by k scales c by k ^ 2.
This is the algebraic reason that a non-primitive solution can be divided down.
-/
theorem fermat42_scale (a b c k : ℤ) (hk : k ≠ 0) :
    Fermat42 a b c ↔ Fermat42 (k * a) (k * b) (k ^ 2 * c) := by
  exact Fermat42.mul hk

/-- In any Fermat42 solution, the square side is also nonzero. -/
theorem fermat42_c_ne_zero {a b c : ℤ} (h : Fermat42 a b c) :
    c ≠ 0 := by
  exact Fermat42.ne_zero h

/-!
## part2. Primitive solutions and coprimality

The descent proof starts by assuming a counterexample and choosing one with
minimal `|c|`. Minimality forces primitivity: if `a` and `b` had a common prime
factor, homogeneity would divide the solution and produce a smaller one.
-/

/-- If a solution exists, a minimal solution exists. -/
theorem exists_minimal_solution {a b c : ℤ} (h : Fermat42 a b c) :
    ∃ a₀ b₀ c₀ : ℤ, Fermat42.Minimal a₀ b₀ c₀ := by
  exact Fermat42.exists_minimal h

/-- A minimal solution is primitive: its two fourth-power bases are coprime. -/
theorem minimal_is_coprime {a b c : ℤ} (h : Fermat42.Minimal a b c) :
    IsCoprime a b := by
  exact Fermat42.coprime_of_minimal h

/-- Swapping the two legs preserves minimality. -/
theorem minimal_swap {a b c : ℤ} :
    Fermat42.Minimal a b c → Fermat42.Minimal b a c := by
  exact Fermat42.minimal_comm

/--
Changing the sign of c preserves minimality, since the proof measures
minimality with Int.natAbs c.
-/
theorem minimal_neg_c {a b c : ℤ} :
    Fermat42.Minimal a b c → Fermat42.Minimal a b (-c) := by
  exact Fermat42.neg_of_minimal

/--
After using symmetry and sign, a counterexample can be normalized:
one leg is odd and the square side is positive.
-/
theorem exists_positive_odd_minimal {a b c : ℤ} (h : Fermat42 a b c) :
    ∃ a₀ b₀ c₀ : ℤ, Fermat42.Minimal a₀ b₀ c₀ ∧ a₀ % 2 = 1 ∧ 0 < c₀ := by
  exact Fermat42.exists_pos_odd_minimal h

/-!
## part3. Connection with Pythagorean triples

From a ^ 4 + b ^ 4 = c ^ 2, the triple (a ^ 2, b ^ 2, c) is a
Pythagorean triple. This is the point where the algebra of squares meets the
classification of primitive Pythagorean triples.
-/

/-- A Fermat42 solution gives a Pythagorean triple. -/
theorem fermat42_to_pythagorean {a b c : ℤ} (h : Fermat42 a b c) :
    PythagoreanTriple (a ^ 2) (b ^ 2) c := by
  delta PythagoreanTriple
  linear_combination h.2.2

/--
The coprimality fact used by the Pythagorean-triple parametrisation:
if r and s are coprime, then r ^ 2 + s ^ 2 is coprime to r * s.
-/
theorem coprime_sq_sum_mul {r s : ℤ} (h : IsCoprime r s) :
    IsCoprime (r ^ 2 + s ^ 2) (r * s) := by
  exact Int.isCoprime_of_sq_sum' h




/-!
## Project-style lemmas for the descent proof

These lemmas split the classical infinite descent argument into named moves.
They deliberately avoid using the finished mathlib theorem `Fermat42.not_minimal`;
the final descent theorem below is assembled from these smaller steps.
-/

/-- A minimal Fermat42 solution gives the Pythagorean triple `(a ^ 2, b ^ 2, c)`. -/
theorem first_triple_from_minimal {a b c : ℤ} (h : Fermat42.Minimal a b c) :
    PythagoreanTriple (a ^ 2) (b ^ 2) c := by
  delta PythagoreanTriple
  linear_combination h.1.2.2

/-- In a minimal Fermat42 solution, the squared legs are coprime. -/
theorem squared_legs_coprime_of_minimal {a b c : ℤ} (h : Fermat42.Minimal a b c) :
    Int.gcd (a ^ 2) (b ^ 2) = 1 := by
  exact Int.isCoprime_iff_gcd_eq_one.mp (Fermat42.coprime_of_minimal h).pow

/-- If `a` is odd, then `a ^ 2` is odd. -/
theorem square_odd_of_odd {a : ℤ} (ha_odd : a % 2 = 1) :
    a ^ 2 % 2 = 1 := by
  rw [sq, Int.mul_emod, ha_odd]
  decide

/-- The identity `a ^ 2 = m ^ 2 - n ^ 2` gives the Pythagorean triple `(a, n, m)`. -/
theorem second_triple_from_difference_of_squares {a m n : ℤ}
    (ha_sq_eq : a ^ 2 = m ^ 2 - n ^ 2) :
    PythagoreanTriple a n m := by
  delta PythagoreanTriple
  linear_combination ha_sq_eq

/-- If `b ^ 2 = 2 * m * n`, then `b` is even. -/
theorem even_of_square_eq_two_mul {b m n : ℤ}
    (hb_sq_eq : b ^ 2 = 2 * m * n) :
    2 ∣ b := by
  apply @Int.Prime.dvd_pow' _ 2 _ Nat.prime_two
  rw [hb_sq_eq, mul_assoc]
  exact dvd_mul_right 2 (m * n)

/-- If `m ≥ 0`, `b ≠ 0`, and `b ^ 2 = 2 * m * n`, then actually `m > 0`. -/
theorem m_pos_of_b_square_eq_two_mul {b m n : ℤ}
    (hb_sq_ne_zero : b ^ 2 ≠ 0)
    (hb_sq_eq : b ^ 2 = 2 * m * n)
    (hm_nonneg : 0 ≤ m) :
    0 < m := by
  apply lt_of_le_of_ne hm_nonneg
  intro hm_zero
  rw [← hm_zero] at hb_sq_eq
  have hb_sq_zero : b ^ 2 = 0 := by
    simpa using hb_sq_eq
  exact hb_sq_ne_zero hb_sq_zero

/-- After writing `b = 2 * b'`, the identities
`b ^ 2 = 2 * m * n` and `n = 2 * r * s` imply `b' ^ 2 = m * (r * s)`. -/
theorem half_square_eq_product {b b' m n r s : ℤ}
    (hb_eq_two_mul_b' : b = 2 * b')
    (hb_sq_eq : b ^ 2 = 2 * m * n)
    (hn_eq : n = 2 * r * s) :
    b' ^ 2 = m * (r * s) := by
  apply (mul_right_inj' (by simp : (4 : ℤ) ≠ 0)).mp
  linear_combination (-b - 2 * b') * hb_eq_two_mul_b' + hb_sq_eq + 2 * m * hn_eq

/-- From the first parametrisation, the second triple has coprime legs. -/
theorem a_n_coprime_from_first_parameters {a m n : ℤ}
    (ha_sq_eq : a ^ 2 = m ^ 2 - n ^ 2)
    (hmn_coprime : Int.gcd m n = 1) :
    Int.gcd a n = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  apply @IsCoprime.of_mul_left_left _ _ _ a
  rw [← sq, ha_sq_eq, (by ring : m ^ 2 - n ^ 2 = m ^ 2 + -n * n)]
  exact (Int.isCoprime_iff_gcd_eq_one.mpr hmn_coprime).pow_left.add_mul_right_left (-n)

/-- In the second parametrisation, `m` is coprime to `r * s`. -/
theorem m_coprime_r_mul_s_from_second_parameters {m r s : ℤ}
    (hm_eq : m = r ^ 2 + s ^ 2)
    (hrs_coprime : Int.gcd r s = 1) :
    Int.gcd m (r * s) = 1 := by
  rw [hm_eq]
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (Int.isCoprime_of_sq_sum' (Int.isCoprime_iff_gcd_eq_one.mpr hrs_coprime))

/-- If a positive integer factor in a coprime square product is square up to sign,
then it is actually a square. -/
theorem positive_square_factor {m r s b' : ℤ}
    (hm_rs_coprime : Int.gcd m (r * s) = 1)
    (hb'_sq_eq : b' ^ 2 = m * (r * s))
    (hm_pos : 0 < m) :
    ∃ i : ℤ, m = i ^ 2 := by
  obtain ⟨i, hm_is_square_or_neg⟩ := Int.sq_of_gcd_eq_one hm_rs_coprime hb'_sq_eq.symm
  have hm_not_neg_square : ¬m = -i ^ 2 := by
    intro h1
    have hnonpos : -i ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg i)
    rw [← h1] at hnonpos
    apply absurd hm_pos (not_lt.mpr hnonpos)
  have hm_eq_i_sq : m = i ^ 2 := by
    exact Or.resolve_right hm_is_square_or_neg hm_not_neg_square
  use i

/-- The other coprime factor in `b' ^ 2 = m * (r * s)` is also a square. -/
theorem product_square_factor {m r s b' : ℤ}
    (hm_rs_coprime : Int.gcd m (r * s) = 1)
    (hb'_sq_eq : b' ^ 2 = m * (r * s))
    (hm_pos : 0 < m)
    (hb'_ne_zero : b' ≠ 0) :
    ∃ d : ℤ, r * s = d ^ 2 := by
  rw [mul_comm] at hb'_sq_eq
  rw [Int.gcd_comm] at hm_rs_coprime
  obtain ⟨d, hrs_is_square_or_neg⟩ := Int.sq_of_gcd_eq_one hm_rs_coprime hb'_sq_eq.symm
  have hrs_not_neg_square : ¬r * s = -d ^ 2 := by
    intro h1
    rw [h1] at hb'_sq_eq
    have hb'_sq_nonpos : b' ^ 2 ≤ 0 := by
      rw [hb'_sq_eq, (by ring : -d ^ 2 * m = -(d ^ 2 * m))]
      exact neg_nonpos.mpr ((mul_nonneg_iff_of_pos_right hm_pos).mpr (sq_nonneg d))
    have hb'_sq_nonneg : 0 ≤ b' ^ 2 := by
      apply sq_nonneg b'
    exact absurd (lt_of_le_of_ne hb'_sq_nonneg (Ne.symm (pow_ne_zero _ hb'_ne_zero)))
      (not_lt.mpr hb'_sq_nonpos)
  have hrs_eq_d_sq : r * s = d ^ 2 := by
    exact Or.resolve_right hrs_is_square_or_neg hrs_not_neg_square
  use d

/-- If `r` and `s` are coprime and `r * s` is a square, then their squares
are fourth powers. -/
theorem fourth_powers_from_coprime_square_product {r s d : ℤ}
    (hrs_coprime : Int.gcd r s = 1)
    (hrs_eq_d_sq : r * s = d ^ 2)
    (hrs_ne_zero : r * s ≠ 0) :
    ∃ j k : ℤ, j ≠ 0 ∧ k ≠ 0 ∧ r ^ 2 = j ^ 4 ∧ s ^ 2 = k ^ 4 := by
  obtain ⟨j, hr_is_square_or_neg⟩ := Int.sq_of_gcd_eq_one hrs_coprime hrs_eq_d_sq
  have hj_ne_zero : j ≠ 0 := by grind
  rw [mul_comm] at hrs_eq_d_sq
  rw [Int.gcd_comm] at hrs_coprime
  obtain ⟨k, hs_is_square_or_neg⟩ := Int.sq_of_gcd_eq_one hrs_coprime hrs_eq_d_sq
  have hk_ne_zero : k ≠ 0 := by grind
  have hr_sq_eq_j_fourth : r ^ 2 = j ^ 4 := by grind
  have hs_sq_eq_k_fourth : s ^ 2 = k ^ 4 := by grind
  apply Exists.intro j
  apply Exists.intro k
  constructor
  · exact hj_ne_zero
  constructor
  · exact hk_ne_zero
  constructor
  · exact hr_sq_eq_j_fourth
  · exact hs_sq_eq_k_fourth

/-- The constructed square side is smaller than the original one. -/
theorem new_square_side_smaller {c i m n : ℤ}
    (hc_pos : 0 < c)
    (hm_eq_i_sq : m = i ^ 2)
    (hc_eq : c = m ^ 2 + n ^ 2)
    (hn_ne_zero : n ≠ 0) :
    Int.natAbs i < Int.natAbs c := by
  apply Int.ofNat_lt.mp
  rw [← Int.eq_natAbs_of_nonneg (le_of_lt hc_pos)]
  apply lt_of_le_of_lt (Int.natAbs_le_self_sq i)
  rw [← hm_eq_i_sq, hc_eq]
  apply lt_of_le_of_lt (Int.le_self_sq m)
  exact lt_add_of_pos_right (m ^ 2) (sq_pos_of_ne_zero hn_ne_zero)



/-!
## Part4. The descent step
-/

/--
The core formalized descent step.

Starting from a normalized minimal solution of `a ^ 4 + b ^ 4 = c ^ 2`,
we classify two primitive Pythagorean triples and construct a new Fermat42
solution with a strictly smaller square side. This contradicts minimality.

Blueprint 1: prove that there is no normalized minimal solution.
-/
theorem no_normalized_minimal {a b c : ℤ}
    (h : Fermat42.Minimal a b c) (ha_odd : a % 2 = 1) (hc_pos : 0 < c) :
    False := by
  have hb_ne_zero : b ≠ 0 := h.1.2.1

  -- Blueprint 2: from `a ^ 4 + b ^ 4 = c ^ 2`, view
  -- `(a ^ 2, b ^ 2, c)` as a Pythagorean triple.
  have ht : PythagoreanTriple (a ^ 2) (b ^ 2) c :=
    first_triple_from_minimal h
  have hsq_coprime : Int.gcd (a ^ 2) (b ^ 2) = 1 :=
    squared_legs_coprime_of_minimal h

  have ha_sq_odd : a ^ 2 % 2 = 1 :=
    square_odd_of_odd ha_odd

  -- Blueprint 3: classify the primitive Pythagorean triple
  -- `(a ^ 2, b ^ 2, c)`, obtaining
  -- `a ^ 2 = m ^ 2 - n ^ 2`, `b ^ 2 = 2 * m * n`,
  -- `c = m ^ 2 + n ^ 2`, and `gcd(m,n)=1`.
  obtain ⟨m, n, ha_sq_eq, hb_sq_eq, hc_eq, hmn_coprime, hmn_parity, hm_nonneg⟩ :=
    ht.coprime_classification' hsq_coprime ha_sq_odd hc_pos

  -- Blueprint 4: from `a ^ 2 = m ^ 2 - n ^ 2`, get the second
  -- Pythagorean triple `(a, n, m)` and prove `gcd(a,n)=1`.
  have htt : PythagoreanTriple a n m :=
    second_triple_from_difference_of_squares ha_sq_eq
  have han_coprime : Int.gcd a n = 1 :=
    a_n_coprime_from_first_parameters ha_sq_eq hmn_coprime
  have hb_sq_ne_zero : b ^ 2 ≠ 0 := pow_ne_zero _ hb_ne_zero
  have hm_pos : 0 < m :=
    m_pos_of_b_square_eq_two_mul hb_sq_ne_zero hb_sq_eq hm_nonneg

  -- Blueprint 5: classify the second primitive Pythagorean triple
  -- `(a, n, m)`, obtaining `n = 2 * r * s`,
  -- `m = r ^ 2 + s ^ 2`, and `gcd(r,s)=1`.
  obtain ⟨r, s, _ha_eq, hn_eq, hm_eq, hrs_coprime, hrs_parity, hr_nonneg⟩ :=
    htt.coprime_classification' han_coprime ha_odd hm_pos

  -- Blueprint 8: record the coprimality needed for the square-factor argument:
  -- `gcd(m, r * s)=1`.
  have hm_rs_coprime : Int.gcd m (r * s) = 1 :=
    m_coprime_r_mul_s_from_second_parameters hm_eq hrs_coprime

  -- Blueprint 6: from `b ^ 2 = 2 * m * n`, show `b` is even.
  have hb_even : 2 ∣ b :=
    even_of_square_eq_two_mul hb_sq_eq
  obtain ⟨b', hb_eq_two_mul_b'⟩ := hb_even

  -- Blueprint 7: write `b = 2 * b'`; using `n = 2 * r * s`,
  -- derive `b' ^ 2 = m * (r * s)`.
  have hb'_sq_eq : b' ^ 2 = m * (r * s) :=
    half_square_eq_product hb_eq_two_mul_b' hb_sq_eq hn_eq
  have hrs_ne_zero : r * s ≠ 0 := by grind
  have hb'_ne_zero : b' ≠ 0 := by grind

  -- Blueprint 9: apply the fact from Blueprint 8 to get
  -- `m = i ^ 2` and `r * s = d ^ 2`, up to sign; positivity removes the signs.
  obtain ⟨i, hm_eq_i_sq⟩ :=
    positive_square_factor hm_rs_coprime hb'_sq_eq hm_pos
  obtain ⟨d, hrs_eq_d_sq⟩ :=
    product_square_factor hm_rs_coprime hb'_sq_eq hm_pos hb'_ne_zero

  -- Blueprint 10: since `r` and `s` are coprime and `r * s` is a square,
  -- get `r ^ 2 = j ^ 4` and `s ^ 2 = k ^ 4`.
  obtain ⟨j, k, hj_ne_zero, hk_ne_zero, hr_sq_eq_j_fourth, hs_sq_eq_k_fourth⟩ :=
    fourth_powers_from_coprime_square_product hrs_coprime hrs_eq_d_sq hrs_ne_zero

  -- Blueprint 11: combine `m = r ^ 2 + s ^ 2`, `m = i ^ 2`,
  -- `r ^ 2 = j ^ 4`, and `s ^ 2 = k ^ 4` to get the new solution equation.
  have hnew_eq : i ^ 2 = j ^ 4 + k ^ 4 := by grind
  have hn_ne_zero : n ≠ 0 := by grind

  -- Blueprint 12: use `c = m ^ 2 + n ^ 2`, `n ≠ 0`, and `m = i ^ 2`
  -- to show the new square side is smaller: `|i| < |c|`.
  have hi_lt_c : Int.natAbs i < Int.natAbs c :=
    new_square_side_smaller hc_pos hm_eq_i_sq hc_eq hn_ne_zero

  -- Blueprint 11, packaged as a `Fermat42` statement for the new triple `(j,k,i)`.
  have hnew_solution : Fermat42 j k i := by
    constructor
    · exact hj_ne_zero
    constructor
    · exact hk_ne_zero
    · exact hnew_eq.symm

  -- Blueprint 13: minimality of `(a,b,c)` says every solution has square side
  -- at least `|c|`; applying it to `(j,k,i)` gives `|c| ≤ |i|`.
  have hc_le_i : Int.natAbs c ≤ Int.natAbs i := by
    exact h.2 j k i hnew_solution

  -- Blueprint 14: Blueprint 12 and Blueprint 13 contradict each other.
  have hnot_le : ¬ Int.natAbs c ≤ Int.natAbs i := by
    exact not_le_of_gt hi_lt_c
  exact hnot_le hc_le_i




/--
The square version of Fermat `n = 4`: no nonzero `a`, `b` satisfy
`a ^ 4 + b ^ 4 = c ^ 2`.
-/
theorem no_square_solution (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 2 :=
  not_fermat_42 ha hb

/--
The hard theorem from mathlib:
there are no nonzero integer `a`, `b` with `a ^ 4 + b ^ 4 = c ^ 2`.
-/
theorem no_fermat42_solution (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 2 :=
  not_fermat_42 ha hb

/--
The exponent-4 integer statement, derived from the square version.
Only the last line is algebra: `c ^ 4 = (c ^ 2) ^ 2`.
-/
theorem fermat_four_int (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 4 := by
  intro h
  apply no_fermat42_solution a b (c ^ 2) ha hb
  calc
    a ^ 4 + b ^ 4 = c ^ 4 := h
    _ = (c ^ 2) ^ 2 := by ring

/-- Existential form of the integer `n = 4` statement. -/
theorem fermat_four_int_no_solution :
    ¬ ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 4 := by
  rintro ⟨a, b, c, ha, hb, h⟩
  exact fermat_four_int a b c ha hb h

/--
Mathlib's official natural-number statement:
Fermat's Last Theorem holds for exponent `4`.
-/
theorem fermat_four_nat : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour
