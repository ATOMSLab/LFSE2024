

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
example : 4/3 = 1 := by rfl
example : 2^(1/2) = 1 := by rfl
example : Nat.sqrt 16 = 4 := by rfl


/-
Thanks to Colin Jones for all these examples!
https://github.com/Colin166/Lean4/blob/main/DerivEx.lean
-/
variable (x y c : ℝ)

/-! Simple goals like these can be solved using `simp?` or `aesop?`. -/
example : deriv (fun _ => c) x = 0 := by simp only [deriv_const']

example : deriv (fun x => x ^ 2) x = 2 * x := by simp only [differentiableAt_id', deriv_pow'',
  Nat.cast_ofNat, Nat.reduceSub, pow_one, deriv_id'', mul_one]

example : deriv (fun x => log x) x = 1 / x := by simp only [deriv_log', one_div]

example : deriv (fun x => exp x) x = exp x := by simp only [Real.deriv_exp]

example : deriv (fun x => sin x) x = cos x := by simp only [Real.deriv_sin]

example : deriv (fun x => cos x) x = - sin x := by simp only [deriv_cos']

/-! Complex goals might need some more -/
example : deriv (fun x => 1/x ) x = - 1/(x^2) := by
  simp only [one_div, deriv_inv']
  ring

-- Types are a difficulty here
example : deriv (fun x => x ^ (-1:ℤ)) x = - x ^ (-2:ℤ) := by
  simp only [Int.reduceNeg, zpow_neg,zpow_one, deriv_inv', neg_inj, inv_inj]
  rfl

example : deriv (fun x => x ^ (-1:ℤ)) x = - x ^ (-2:ℤ) := by
  rw [show - x ^ (-2 :ℤ) = (-1:ℤ ) * x ^(-2:ℤ) by ring]
  apply deriv_zpow

example : deriv (fun x => x ^ (-2:ℤ)) x = (-2:ℤ) * x ^ (-3:ℤ) := by
  rw [show (-3: ℤ) = -2 -1 by ring]
  apply deriv_zpow

example (hx : x ≠ 0) : deriv (fun x => x ^ (-2 : ℝ)) x = (-2) * x ^ (-3 : ℝ) := by
  rw [show (-3:ℝ) = -2 -1 by ring]
  simp_all only [ne_eq, differentiableAt_id', not_false_eq_true, true_or, _root_.deriv_rpow_const, deriv_id'', mul_neg,
    one_mul, neg_mul]

example (hx : x ≠ 0) : deriv (fun x => x ^ (-2 / 3 : ℝ)) x = (-2 / 3) * x ^ (-5 / 3 : ℝ) := by sorry

/-! Product rules begin with `rw [deriv_mul]`
This generates 3 goals to prove.
Access each goal one-by-one using the centerdot ·
Note that centerdot is different from cdot ⬝ -/
example : deriv (fun x => x * sin x) x = sin x + x * cos x := by
  rw [deriv_mul]
  · simp only [deriv_id'', one_mul, Real.deriv_sin]
  · fun_prop
  · exact differentiableAt_sin

example : deriv (fun x => x ^ 2 * cos x) x = 2 * x * cos x - x ^ 2 * sin x := by
  rw [deriv_mul]
  · simp_all only [differentiableAt_id', deriv_pow'', Nat.cast_ofNat, Nat.reduceSub, pow_one, deriv_id'', mul_one,
    deriv_cos', mul_neg]
    ring
  · fun_prop
  · exact differentiableAt_cos

example : deriv (fun x => sin x * cos x) x = (cos x) ^ 2 - (sin x) ^ 2 := by
  rw [deriv_mul]
  · sorry
  · sorry
  · sorry

-- Writing proofs about functions defined outside the theorem
variable (k x_eq : ℝ)
noncomputable def force (x : ℝ) : ℝ := -k*(x - x_eq)
noncomputable def energy (x : ℝ) : ℝ := (k/2)*(x - x_eq)^2

#check force

example : deriv (energy k x_eq) x = - force k x_eq x := by
  dsimp [force]
  rw [show energy k x_eq = fun x:ℝ => (k/2)*(x - x_eq)^2 by rfl]
  simp
  ring
