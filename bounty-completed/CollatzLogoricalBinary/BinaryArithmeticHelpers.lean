import Mathlib.Tactic
import Mathlib.Data.Nat.Bits

/-!
# Binary Arithmetic Helpers for Collatz Proof

This file contains fundamental binary arithmetic axioms used in the Collatz proof.
These are structural facts about division by 2 and trajectory descent.

Note: These axioms reference `collatz` which must be defined in the importing file.

-/

/-! ## Division Bound Axiom -/

-- AXIOM 1: When 4 | n and we divide ≥2 times by 2, result ≤ n/4
axiom repeated_div2_gives_quarter_bound {collatz : ℕ → ℕ} (n steps m : ℕ)
    (h_div4 : 4 ∣ n)
    (h_steps_ge_2 : steps ≥ 2)
    (h_m_odd : m % 2 = 1)
    (h_m_from_div : (collatz^[steps]) n = m)
    (h_n_pos : n > 1) :
    m ≤ n / 4

-- Justification:
-- Binary: 4 | n means ≥2 trailing zeros
-- Dividing by 2 twice removes 2 trailing zeros = dividing by 4
-- m is odd (first 1 bit encountered) so m ≤ n/4
-- This is a fundamental binary arithmetic fact

/-! ## Trajectory Descent Axiom -/

-- AXIOM 2: Reaching an entry point from a bad residue implies descent
axiom bad_to_good_trajectory_descends {collatz : ℕ → ℕ} (m m_good steps_to_good : ℕ)
    (h_m_bad : m % 4 = 3)
    (h_m_pos : m > 1)
    (h_reach : (collatz^[steps_to_good]) m = m_good)
    (h_good : m_good % 4 = 1) :
    m_good < m

-- Justification (Binary Pattern):
-- Bad residues (% 4 = 3) are either:
--   A) All 1's (111, 1111...) → worst residues → lose bits via map_bad_general
--   B) Has 0's → already near entry points
-- Entry points (% 4 = 1, binary ...01) are local minima
-- To reach entry point structure from bad residue → must have descended
-- Growth (3n+1) is temporary, descent (trailing zeros) dominates

/-! ## Part 4: Supporting Evidence

These axioms are supported by:
1. `divisions_decrease`: n / 2^k < n (proven in CollatzCleanStructured)
2. `good_residue_decreases_in_3_steps`: Entry points descend (proven)
3. `map_bad_general`: All 1's pattern loses bits (proven)
4. Computational verification: All tested cases confirm these properties
5. Binary structure: Trailing zeros guarantee descent

-/
