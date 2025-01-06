import Mathlib

/-
The have tactic: Proofs using intermediate steps
Example 2.1.1 from MoP
-/
example {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3) :
  a = 9 := by
  have hb : b = 1 := by linarith
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

--Should you use have, or add a hypothesis? What's the difference?

example {a b : ℝ}
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  (hb : b = 1):
  a = 9 := by
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

-- How to catch a contradiction using slimcheck
example {a b : ℕ} (h1: a - b = a + b) : a = 5 := by
  slim_check

-- Unfortunately for our problem, slim_check runs out of time
example {a b : ℕ }
  (h1 : a - 5 * b = 4)
  (h2 : b + 2 = 3)
  (hb : b = 2):
  a = 9 := by
  slim_check

/-
Proofs using existing lemmas
Example 2.2.1 from MoP
-/

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  sorry -- can't use norm_num

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt -- changes the proof goal to an inequality
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by norm_num


-- Lean is not a calculator! (yet)
-- norm_num doesn't know how to handle this
example : Real.sqrt 2 ≤ 3 := by norm_num

-- But - we can help it along by giving it access to a helpful theorem
example : Real.sqrt 2 ≤ 3 := by
  norm_num [Real.sqrt_le_iff] -- providing a theorem TO a tactic

-- Why doesn't norm_num check all the theorems first? Efficiency and "scope creep"






/-
I have 20 minutes to make a return to a UPS store before they all close at 5:00 pm.
I can make my return at any UPS store.
One UPS store is 5 miles away; I can drive and average of 50 miles/hour to get there.
One UPS store is 1 mile away, but I’ll need to average 30 miles/hour during that drive.
Can I make the return in time?
-/

-- Prove that either time1 or time2 is less than or equal to 1/3
-- 1/3 is 20 minutes converted to hours
example {distance1 speed1 distance2 speed2 time1 time2 : ℝ}
  (h1 : distance1 = 5)
  (h2 : speed1 = 50)
  (h3 : distance2 = 1)
  (h4 : speed2 = 30)
  (h5 : time1 = distance1/speed1)
  (h6 : time2 = distance2/speed2) :
  time1 ≤ 1/3 ∨ time2 ≤ 1/3 := by
  left -- using left sets up a proof for the left side of "or"
  calc
    time1 = distance1/speed1 := by rw [h5]
    _ = 5/50 := by rw [h1, h2]
    _ ≤ 1/3 := by norm_num

example {distance1 speed1 distance2 speed2 time1 time2 : ℝ}
  (h1 : distance1 = 5)
  (h2 : speed1 = 50)
  (h3 : distance2 = 1)
  (h4 : speed2 = 30)
  (h5 : time1 = distance1/speed1)
  (h6 : time2 = distance2/speed2) :
  time1 ≤ 1/3 ∨ time2 ≤ 1/3 := by
  right -- using right sets up a proof for the right side of "or"
  calc
    time2 = distance2/speed2 := by rw [h6]
    _ = 1/30 := by rw [h3, h4]
    _ ≤ 1/3 := by norm_num

/-
A paratrooper jumps off a cliff and opens a parachute immediately at 300 meters.
His weight is 90kg and he has a parachute that can provide air resistance up to 875N.
Will the parachute be able to handle the descending force,
so that the soldier lands at a safe speed less than or equal to 7m/s, and
will he reach the ground (0 meters) in 100 seconds so that enemy sensors cannot target him?
-/
example {height weight parachute_resist net_resist acceleration time Svelocity: ℝ}
(h1 : height = 300)
(h2 : weight = 90)
(h3 : parachute_resist = 875)
(h4 : net_resist = (weight * 9.8) - parachute_resist)
(h5 : acceleration = net_resist/weight)
(h6 : time = (2 * height / (acceleration))^(1/2) )
(h7 : Svelocity = acceleration * time) :
time ≤ 100 ∧ Svelocity ≤ 7:= by
  constructor -- splits the "and" goal into two subgoals
  calc
    time = (2 * height / (acceleration))^(1/2) := by rw [h6]
    _= (2 * 300 / (net_resist/weight))^(1/2) := by rw [h5, h1]
    _= (2 * 300 / (((weight * 9.8) - parachute_resist)/weight))^(1/2) := by rw [h4]
    _= (2 * 300 / (((90 * 9.8) - 875)/90))^(1/2) := by rw [h2, h3]
    _ ≤ 100 :=  by norm_num
  calc
    Svelocity = acceleration * time := by rw[h7]
    _ = acceleration * (2 * height / (acceleration))^(1/2) := by rw [h6]
    _ = net_resist/weight * (2 * height / (net_resist/weight))^(1/2) := by rw [h5]
    _ = ((weight * 9.8) - parachute_resist)/90 * (2 * 300 / (((weight * 9.8) - parachute_resist)/90))^(1/2)
     := by rw [h4, h1 ,h2]
    _ = ((90 * 9.8) - 875)/90 * (2 * 300 / (((90 * 9.8) - 875)/90))^(1/2) := by rw [h2, h3]
    _ ≤ 7 := by norm_num

-- Watch out! Number types are tricky things.
example {height weight parachute_resist net_resist acceleration time Svelocity: ℝ}
(h1 : height = 300)
(h2 : weight = 90)
(h3 : parachute_resist = 875)
(h4 : net_resist = (weight * 9.8) - parachute_resist)
(h5 : acceleration = net_resist/weight)
(h6 : time = Real.sqrt (2 * height / (acceleration)))
(h7 : Svelocity = acceleration * time) : time ≤ 100 ∧ Svelocity ≤ 7:= by

  constructor -- splits the "and" goal into two subgoals
  calc
    time = Real.sqrt (2 * height / (acceleration)) := by rw [h6]
    _ = Real.sqrt (2 * 300 / (net_resist/weight)) := by rw [h5, h1]
    _ = Real.sqrt (2 * 300 / (((weight * 9.8) - parachute_resist)/weight)) := by rw [h4]
    _ = Real.sqrt (2 * 300 / (((90 * 9.8) - 875)/90)) := by rw [h2, h3]
    _ = Real.sqrt (2 * 300 * 90 / (90 * 9.8 - 875)) := by field_simp
    _ = Real.sqrt (54000 / 7) := by ring_nf
    _ ≤ 100 := by rw [Real.sqrt_le_iff] <;> norm_num
  calc
    Svelocity = acceleration * time := by rw[h7]
    _ = acceleration * Real.sqrt (2 * height / (acceleration)):= by rw [h6]
    _ = net_resist/weight * Real.sqrt (2 * height / (net_resist/weight)) := by rw [h5]
    _ = ((weight * 9.8) - parachute_resist)/90 * Real.sqrt (2 * 300 / (((weight * 9.8) - parachute_resist)/90))
     := by rw [h4, h1 ,h2]
    _ = ((90 * 9.8) - 875)/90 * Real.sqrt (2 * 300 / (((90 * 9.8) - 875)/90)) := by rw [h2, h3]
    _ = ((90 * 9.8) - 875)/90 * Real.sqrt (2 * 300 * 90 / (90 * 9.8 - 875)) := by field_simp
    _ = 7/90 * Real.sqrt (54000 / 7) := by ring_nf
     _ = Real.sqrt ((7^2 / 90^2) * (54000 / 7)) := by field_simp
    _ ≤ 7 := by rw [Real.sqrt_le_iff] <;> norm_num


--  have sq: (Real.sqrt (54000 / 7))^2 ≤ 100 := by norm_num [Real.sqrt_le_iff]
