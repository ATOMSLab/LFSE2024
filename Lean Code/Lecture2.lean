import Mathlib

-- A plane flies 450 miles with the wind in 3 hours
-- Flying back against the wind, the plane takes 5 hours to make the trip
-- Prove that the plane's speed in still air would be 120 miles/hour

-- Natural way to set up the problem, recognizing that d = v*t
-- Plane's velocity is x, wind velocity is y
-- First trip, with the wind:  d = (x + y)*t
-- Second trip, against the wind: d = (x - y)*t
example {x y : ℝ}
(h1 : 450 = (x + y)*3 )
(h2 : 450 = (x - y)*5 )
: x = 120 :=
by sorry

-- Simpler way to set up the problem (easier to prove in Lean)
example {x y : ℝ}
(h1 : x + y = 150)
(h2 : x - y = 90)
: x = 120 :=
calc
  x = ((x - y) + (x + y)) / 2 := by ring  -- algebraic rearrangement
  _ = (90 + 150) / 2 := by rw [h1, h2] -- substitution
  _ = 120 := by ring -- algebraic rearrangement


/-
Let's practice calculation-based proofs, first, by filling in tactics
Think of a proof like a maze: you have many possible paths to take,
some make progress toward the goal, but others lead toward dead ends.
The below examples show completed solutions (a solved maze), and
we're supposed to justify the steps along the way,
not necessarily finding the way on our own
but proving that the given solution is correct.
-/

/-
A resistor has a resistance of 4 Ohms and a current of 3 Amps flows through it.
Prove that the voltage across the resistor is 12 Volts.
-/
example {v I R : ℝ}
(h1 : I = 3)
(h2 : R = 4)
(h3 : v = I * R) : v = 12 :=
calc
v = I * R := by sorry
_ = 3 * R := by sorry
_ = 3 * 4 := by sorry
_ = 12 := by sorry

-- Example 1.2.1 from MoP
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by sorry -- algebraic rearrangement
    _ = 4 ^ 2 + 4 * 1 := by sorry -- substitution
    _ = 20 := by sorry -- simplification

-- Example 1.2.2 from MoP
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by sorry
    _ = -1 - 2 * s := by sorry
    _ = -1 - 2 * 3 := by sorry
    _ = -7 := by sorry

-- rw is "rewrite" - useful for substitution
-- "algebraic rearrangement" can be accomplished by tactics like simp, ring, linarith, norm_num


-- Example 1.2.3 from MoP
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 := by sorry

-- Example 1.2.4 from MoP
-- No roadmap for you! Can you figure out how to start?
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  sorry

-- Inequalities

/- A toy mouse changes speed from a constant 2 m/s to 0 m/s in the span of two seconds.
It's mass is estimated to be around 0.1 kg.
The toy can only handle two Newtons of force.
Prove that the force it experiences is below this limit. -/

theorem toy_mouse_force_limit {f :ℝ }
(h1:v₀=2)
(h2:v₁=0)
(h3:m=0.1)
(h4:t=2)
(h5:a=(v₁ - v₀) / t)
(h6:f= m *a) :f < 2 := by
calc
f=m * a := by sorry
_=m*((v₁ - v₀) / t ):= by sorry
_= 0.1*((0  - 2) / 2 ) := by sorry
_ < 2 :=by sorry


-- Example 1.4.1 from MoP
-- Introduces the tactic 'rel' for relational substitution
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by norm_num

-- Note that the powerful linarith tactic proves this in one shot
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y > 3 := by linarith

-- Example 1.4.2 from MoP
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by sorry
    _ ≤ (3 + (s + 3) - s) / 2 := by sorry
    _ = 3 := by sorry

-- Example 1.4.3 from MoP
-- No "roadmap" for this one - can you figure out how to start?
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  sorry


-- MoP Ch 1 has many more practice problems

-- FYI - many tactics can solve simple number relationships
example :5 ≠ 6:=by norm_num
example :9>4:=by linarith
example :2^2=4 :=by simp
