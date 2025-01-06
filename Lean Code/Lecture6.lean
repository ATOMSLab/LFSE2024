

import Mathlib
open Real

-- Examples of currying
#check Nat.mul
#check Nat.mul 5
#check Nat.mul 5 2

/- Junk values -/

example : 1/0 = 0 := by rfl
example : 1-2 = 0 := by rfl

/- Weird, but makes sense if you think about number systems
and notice that ℕ is the type inferred here -/
example : 4/3 = ? := by rfl
example : 2^(1/2) = ? := by rfl
example : Nat.sqrt 8 = ? := by rfl


/-
Thanks to Colin Jones for all these examples!
https://github.com/Colin166/Lean4/blob/main/DerivEx.lean
-/
variable (x y c : ℝ)

/-! Simple goals like these can be solved using `simp?` or `aesop?`. -/
example : deriv (fun _ => c) x = 0 := by sorry

example : deriv (fun x => x ^ 2) x = 2 * x := by sorry

example : deriv (fun x => log x) x = 1 / x := by sorry

example : deriv (fun x => exp x) x = exp x := by sorry

example : deriv (fun x => sin x) x = cos x := by sorry

example : deriv (fun x => cos x) x = - sin x := by sorry

/-! Complex goals might need some more -/
example : deriv (fun x => 1/x ) x = - 1/(x^2) := by sorry

-- Types are a difficulty here
example : deriv (fun x => x ^ (-1:ℤ)) x = - x ^ (-2:ℤ) := by sorry

example : deriv (fun x => x ^ (-2:ℤ)) x = (-2:ℤ) * x ^ (-3:ℤ) := by sorry

example (hx : x ≠ 0) : deriv (fun x => x ^ (-2 : ℝ)) x = (-2) * x ^ (-3 : ℝ) := by sorry

example (hx : x ≠ 0) : deriv (fun x => x ^ (-2 / 3 : ℝ)) x = (-2 / 3) * x ^ (-5 / 3 : ℝ) := by sorry

/-! Product rules begin with `rw [deriv_mul]`
This generates 3 goals to prove.
Access each goal one-by-one using the centerdot ·
Note that centerdot is different from cdot ⬝ -/
example : deriv (fun x => x * sin x) x = sin x + x * cos x := by
  rw [deriv_mul]
  · sorry
  · sorry
  · sorry

example : deriv (fun x => x ^ 2 * cos x) x = 2 * x * cos x - x ^ 2 * sin x := by
  rw [deriv_mul]
  · sorry
  · sorry
  · sorry

example : deriv (fun x => sin x * cos x) x = (cos x) ^ 2 - (sin x) ^ 2 := by
  rw [deriv_mul]
  · sorry
  · sorry
  · sorry



-- Writing proofs about functions defined outside the theorem
variable (k x_eq : ℝ)
noncomputable def force (x : ℝ) : ℝ := -k*(x - x_eq)
noncomputable def energy (x : ℝ) : ℝ := (k/2)*(x - x_eq)^2

example : deriv (energy k x_eq) x = - force k x_eq x := by
  sorry
