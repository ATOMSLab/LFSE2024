import Mathlib

-- Exists, Example 3.1.1 from MoP
def MyOdd (a : ℤ) : Prop := ∃ k, a = 2 * k + 1

-- Solve using k=3 as a witness
example : MyOdd (7:ℤ) := by
  sorry

-- Same example using Odd from Mathlib
example : Odd (7:ℤ) := by
  sorry

-- Mathlib has cool tactics that don't require you to provie a witness
example : Odd (7:ℤ) := by
  decide

-- But decide doesn't know about MyOdd, which isn't in Mathlib
example : MyOdd (7:ℤ) := by
  decide

-- Huckel's rule describes conditions for aromaticity of cyclic molecules.
-- M is the number of pi electrons in a ring system and n is some natural number.
-- Huckel's rule says that the number of electrons must be able to satisfy 4*n + 2
-- We state this as "there exists some n such that M = 4*n + 2"
-- We can solve this using a witness - by stating that for M = 6, n=1 is a solution
example {M : Nat} (h1: M = 6) : ∃ n, (M = 4*n + 2) := by
  use 1 -- for some reason, use also performs numerical simplication and closes the goal


-- A cooler way to define Huckel's Rule is by counting electron *pairs*
-- The molecule is aromatic if it has an odd number of electron pairs,
-- and anti-aromatic if it the number of electron pairs is even
example {M : Nat} (h1: M = 6) : ∃ n, ((M = 2*n) ∧ (Odd n)) := by
  sorry

example {M : Nat} (h1: M = 6) : ∃ n, ((M = 2*n) ∧ (Odd n)) := by
  sorry

-- Let's create a definition for the concept of aromaticity
def aromatic (M : Nat) : Prop := ∃ n, (M = 4*n + 2)
def aromatic2 (M : Nat) : Prop := ∃ n, ((M = 2*n) ∧ (Odd n))

-- With this, we can create a more generic setup
example (h1: benzene_M = 6) : (aromatic2 benzene_M) := by
  sorry


-- For all
-- Prove that x squared is always positive
theorem square_positive : ∀ (x : ℝ), x^2 ≥ 0 := by
  intro x
  exact sq_nonneg x


-- Example 4.1.1
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by norm_num

-- Newton's second law:
-- When net force is zero, that implies that acceleration is zero
theorem zero_force_zero_acceleration {F m a : ℝ }
  (h1 : F = m*a)
  (h2 : m > 0):
  F = 0 → a = 0 := by
  sorry
