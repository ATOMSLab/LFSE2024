import Mathlib

#eval 0.1 + 0.2 > 0.3

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
by polyrith

-- Simpler way to set up the problem (easier to prove in Lean)
example {x y : ℝ}
(h1 : x + y = 150)
(h2 : x - y = 90)
: x = 120 :=
calc
  x = ((x - y) + (x + y)) / 2 := by ring  -- algebraic rearrangement
  _ = (90 + 150) / 2 := by rw [h1, h2] -- substitution
  _ = 120 := by norm_num -- numerical simplication


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
A resistor has a resistance of 4 Ohms
and a current of 3 Amps flows through it.
Prove that the voltage across the resistor is 12 Volts.
-/
example {v I R : ℝ}
(h1 : I = 3)
(h2 : R = 4)
(h3 : v = I * R) : v = 12 :=
calc
v = I * R := by rw [h3]
_ = 3 * R := by rw [h1]
_ = 3 * 4 := by rw [h2]
_ = 12 := by norm_num

-- Example 1.2.1 from MoP
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring -- algebraic rearrangement
    _ = 4 ^ 2 + 4 * 1 := by rw [h1,h2] -- substitution
    _ = 20 := by norm_num -- numerical simplification

-- Example 1.2.2 from MoP
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by norm_num

-- rw is "rewrite" - useful for substitution
-- "algebraic rearrangement" can be accomplished by tactics like simp, ring, linarith, polyrith


-- Example 1.2.3 from MoP
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw [h1, h2]
    _ = 2 := by norm_num

-- Example 1.2.4 from MoP
-- No roadmap for you! Can you figure out how to start?
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = (a * d) * f - b * (d * e) := by ring
    _ = (b * c) * f - b * (c * f) := by rw [h1,h2]
    _ = 0 := by ring

-- Inequalities

/- A toy mouse changes speed from a constant 2 m/s to 0 m/s
in the span of two seconds.
It's mass is estimated to be around 0.1 kg.
The toy can only handle two Newtons of force.
Prove that the force it experiences is below this limit. -/

theorem toy_mouse_force_limit {f v₀ v₁ m t a :ℝ }
(h1:v₀=2)
(h2:v₁=0)
(h3:m=0.1)
(h4:t=2)
(h5:a=(v₁ - v₀) / t)
(h6:f= m *a) :f < 2 := by
calc
  f=m * a := by rw [h6]
  _=m*((v₁ - v₀) / t ):= by rw [h5]
  _= 0.1*((0  - 2) / 2 ) := by rw [h1, h2, h3, h4]
  _ < 2 :=by norm_num


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
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h1,h2]
    _ = 3 := by ring

-- Example 1.4.3 from MoP
-- No "roadmap" for this one - can you figure out how to start?
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y = x + y := by ring
    _ ≤ x + (x + 5) := by rel [h1]
    _ ≤ -2 + (-2 + 5) := by rel [h2]
    _ < 2 := by norm_num


-- MoP Ch 1 has many more practice problems - solve those to build your skills!


/- You might find that many tactics can solve the same kinds of goals
Sometimes, all you want to do is close the goal, and anything will do.
But it's best practice to choose the tactic that most aligns with the goal
that needs closing - other, more powerful steps may work but be less efficient.

For example, linarith and norm_num can both prove that 9 > 4,
but norm_num is more efficient (as measured below by "heartbeats")
-/

count_heartbeats in -- 1142 heartbeats
example :9>4:=by linarith
count_heartbeats in -- 146 heartbeats -- nearly 10 times quicker
example :9>4:=by norm_num
