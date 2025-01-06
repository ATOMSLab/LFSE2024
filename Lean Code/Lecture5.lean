import Mathlib
open Classical

/-
Types!
Look at exercises in Chapter 2 of Theorem Proving in Lean 4
-/

-- Type checking doesn't care about names of variables
-- Example from Bulhwi Cha
def force (m a : ℝ) : ℝ := m * a
def voltage (I R : ℝ) : ℝ := I * R
theorem force_eq_voltage : force = voltage := by rfl



-- A petri dish contains 100 counts of bacteria which doubles every 3 hours.
-- (a) Write a formula that expresses the
-- population as a function of time in hours.
-- (b) What will the population be after 4 hours, 6 hours, and 14 hours?
-- This is also a computable function, since Lean can generate bytecode
-- for this function.

def population : ℕ → Float
| t => 100.0 * (2.0 ^ ((t.toFloat) / 3.0))
-- 100.0 - starting population
-- 2.0 - popultion double factor
-- t.toFloat / 3.0 - time used to double

def population2 : ℕ → ℚ
| t => 100.0 * (2 ^ ((t) / (3:ℚ)))
-- 100.0 - starting population
-- 2.0 - popultion double factor
-- t.toFloat / 3.0 - time used to double

#eval population 4
#eval population 6
#eval population 14

-- Example of the noncomputable funciton, choice assumes the set is nonempty
-- this means only nonempty sets can only be passed
noncomputable def indefiniteDescription1 {α : Sort u} (p : α → Prop)
(h : ∃ x, p x) : {x // p x} :=
choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩ -- let ⟨x, px⟩ := h extraxts the x and px
-- choice function chooses an arbitrary x that satisfies p and this creates the subtype {x // p x}

-- grabs the first element
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
(indefiniteDescription1 p h).val


/- Examples of functions in science and engineering -/

-- Current as a function of time
noncomputable def current_real (t : ℝ) : ℝ  := Real.cos t
def current_Float (t : Float) : Float  := Float.cos t
#check current_real

-- Function with discrete domain
def switch : Bool → ℝ
  | Bool.true  => 55.5
  | Bool.false => 0

def choices : ℕ → ℝ
  | 0 => 55.5
  | 1 => 23
  | _ => 0

-- Lean uses match to map discrete values in the domain to
-- outputs in the co-domain


/- Defining pressure and volume as "state functions"
Mapping some state (indexed by the natural numbers) to ℝ
-/
variable (pressure : ℕ → ℝ)
variable (volume : ℕ → ℝ)

-- Note, we can do this more generally with a generic type

def Boyle's_Law  : Prop := ∃ (k : ℝ), ∀ n, (pressure n)*(volume n) = k
def Boyle's_Law2 : Prop := ∀ n m, (pressure n)*(volume n) = (pressure m)*(volume m)

theorem boyles_law_relation:
  Boyle's_Law pressure volume → Boyle's_Law2 pressure volume := by
  intros h n m
  dsimp [Boyle's_Law] at h
  rcases h with ⟨k, hk⟩
  field_simp [hk]

theorem boyles_law_relation' (n₀  :ℕ  ): Boyle's_Law2 pressure volume → Boyle's_Law pressure volume := by
  intro h
  apply Exists.intro (pressure  n₀  * volume n₀  )
  intro n
  exact h n n₀

-- Other useful tactics
