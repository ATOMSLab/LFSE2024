import Mathlib

-- A plane flies 450 miles with the wind in 3 hours
-- Flying back against the wind, the plane takes 5 hours to make the trip
-- Prove that the plane's speed in still air would be 120 miles/hour

-- Natural way to set up the problem, recognizing that d = v*t
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
  x = ((x - y) + (x + y)) / 2 := by ring
  _ = (90 + 150) / 2 := by rw [h1, h2]
  _ = 120 := by ring


theorem Boyle {P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ}
-- Assumptions
(h1: P1*V1 = n1*R*T1)
(h2: P2*V2 = n2*R*T2)
(h3: T1=T2)
(h4: n1=n2) :
-- Conjecture
(P1*V1 = P2*V2) :=
-- Proof
by
  rw [h3] at h1
  rw [h4] at h1
  rw [← h2] at h1
  exact h1

-- Short proof
example {P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ}
(h1: P1*V1 = n1*R*T1)
(h2: P2*V2 = n2*R*T2)
(h3: T1=T2)
(h4: n1=n2) :
(P1*V1 = P2*V2) :=
by
  rw [h1, h2, h3, h4]

-- Proof with calc block (style taught in MoP Ch. 1)
example {P1 P2 V1 V2 T1 T2 n1 n2 R : ℝ}
(h1: P1*V1 = n1*R*T1)
(h2: P2*V2 = n2*R*T2)
(h3: T1=T2)
(h4: n1=n2) :
(P1*V1 = P2*V2) :=
by
  calc
  P1*V1 = n1*R*T1 := by rw [h1]
  _ = n2 * R * T2 := by rw [h3, h4]
  _ = P2*V2 := by rw [h2]
