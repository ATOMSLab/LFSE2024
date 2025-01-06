import Mathlib

/- Do notation -/

def factorial_do (n : Nat) : Nat := Id.run do
  let mut result := 1
  for i in [1:n+1] do
    result := result * i
  return result

#eval factorial_do 5  -- Expected output: 120



/- Polymorphism -/

-- Defining a polymorphic structure (from FPIL 1.6)
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

-- Define an origin where x and y are natural numbers

-- Define an origin where x and y are floats



-- Defining a polymorphic identity function
def identity {α : Type} (x : α) : α := x

-- Use the identity function with different types
#eval identity 5       -- Output: 5
#eval identity "hello" -- Output: "hello"


-- Another polymorphic function
def plusOne [Add α] [One α] (inputVal : α) : α :=
  inputVal + 1

-- Let's do a calculation with Float
#eval plusOne (1.5)

-- Let's write a proof with ℝ
-- This is about injectivity, or "is a function one-to-one?"
def functionIsOneToOne (f : X → Y) : Prop :=
  ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2

theorem PlusOneIsInjective : functionIsOneToOne (plusOne : ℝ → ℝ) := by
  dsimp [functionIsOneToOne]
  intro x1 x2 h
  dsimp [plusOne] at h
  linarith [h]

-- Langmuir Adsorption Equation
noncomputable def Langmuir (K_eq : ℝ ) (P : ℝ ) : ℝ :=
  K_eq * P / (1 + K_eq*P)

-- We can't do calculations!
#eval Langmuir 5.0 9.0

-- We can do proofs

theorem LangmuirAdsorption {θ K P r_ad r_d k_ad k_d A S_tot S : ℝ}
  (hrad : r_ad = k_ad * P * S) -- Adsorption rate expression
  (hrd : r_d = k_d * A)        -- Desorption rate expression
  (heq : r_ad = r_d)           -- Equilibrium assumption
  (hK : K = k_ad / k_d)        -- Definition of adsorption constant
  (hS_tot : S_tot = S + A)     -- Site balance
  (hθ : θ = A / S_tot)         -- Definition of fractional coverage
  -- Physical constraints
  (hc1 : S + A ≠ 0)
  (hc2 : k_d + k_ad * P ≠ 0)
  (hc3 : k_d ≠ 0) :
  θ = Langmuir K P := by
  dsimp [Langmuir]
  rw [hrad, hrd] at heq
  rw [hθ, hS_tot, hK]
  field_simp
  calc
    A * (k_d + k_ad * P) = k_d * A + k_ad * P * A := by ring
    _ = k_ad * P * S + k_ad * P * A := by rw[heq]
    _ = k_ad * P * (S + A) := by ring


/- Lists in Lean -/
-- Example from FPIL 1.6
def primesUnder10 : List Nat := [2, 3, 5, 7]

-- You can
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

theorem equivalence : primesUnder10 = explicitPrimesUnder10 := by rfl

-- Let's add up the elements in the list
def sum_list : List Nat → Nat
  | [] => 0
  | (x :: xs) => x + sum_list xs

#eval sum_list [2,4,5]
#eval sum_list primesUnder10

-- Lessons learned: empty list is the useful base case
-- Functions are recursive

def square_list : List Nat → List Nat
  | [] => []
  | (x :: xs) => (x * x) :: square_list xs

#eval square_list [2,3]




def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)


-- Example from Oscar Matemb
def periodicTable : List String := /-Elemnts of the periodic table by symbol-/
  ["H", "He", "Li", "Be", "B", "C", "N", "O", "F", "Ne", "Na", "Mg", "Al", "Si", "P", "S", "Cl", "Ar", "K", "Ca",
  "Sc", "Ti", "V", "Cr", "Mn", "Fe", "Co", "Ni", "Cu", "Zn", "Ga", "Ge", "As", "Se", "Br", "Kr", "Rb", "Sr", "Y", "Zr",
  "Nb", "Mo", "Tc", "Ru", "Rh", "Pd", "Ag", "Cd", "In", "Sn", "Sb", "Te", "I", "Xe", "Cs", "Ba", "La", "Ce", "Pr", "Nd",
  "Pm", "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb", "Lu", "Hf", "Ta", "W", "Re", "Os", "Ir", "Pt", "Au", "Hg",
  "Tl", "Pb", "Bi", "Po", "At", "Rn", "Fr", "Ra", "Ac", "Th", "Pa", "U", "Np", "Pu", "Am", "Cm", "Bk", "Cf", "Es", "Fm",
  "Md", "No", "Lr", "Rf", "Db", "Sg", "Bh", "Hs", "Mt", "Ds", "Rg", "Cn", "Nh", "Fl", "Mc", "Lv", "Ts", "Og"]

def hedgehog := periodicTable[0]
def deer := periodicTable[1]
def snail := periodicTable[2]



/-count all characters in all symbols of the periodic table-/
def totalCharacters : Nat :=
  periodicTable.foldl (fun pT s => pT + s.length) 0

/- count elements with names longer than 2 characters-/
def countLongNames (symbols : List String) : Nat :=
  symbols.foldl (fun pT symbol => if symbol.length > 2 then pT + 1 else pT) 0

/-return symbols with a certain letter e.g., letter t-/
def elementsByLetter : List String := periodicTable.filter (fun pT => pT.contains 't')

/- Find an element by index-/
def elementIndex (idx : Nat) : String :=
  if pT : idx < periodicTable.length then (periodicTable.get ⟨idx, pT⟩)
  else "none"


-- From Lecture 7

structure Chemprop where
  name       : String
  symbol     : String
  atomicNum  : Nat
  atomicMass : Float
  electronegativity :  Float
deriving Repr


structure Molecule where
  name     : String
  formula  : String
  typeOfAtoms : List Chemprop
  numOfAtoms : List Float
deriving Repr


/-- Examples of Elements below
a molecule of water, made up of two H atoms and one O₂ atom
--/
def hydrogen : Chemprop :=
  { name := "Hydrogen", symbol := "H", atomicNum := 1, atomicMass := 1.00794, electronegativity := 2.20}

def oxygen : Chemprop :=
  { name := "Oxygen", symbol := "O", atomicNum := 8, atomicMass := 15.9996, electronegativity := 3.44}

-- Example of a Molecule (Water - H2O)
def water : Molecule :=
  { name := "Water", formula := "H2O", typeOfAtoms := [hydrogen, oxygen] , numOfAtoms := [2, 1]}

-- Pattern matching is done automatically with the lambda function
def molWeight (M : Molecule) : Float :=
  -- foldl folds the list to the left to combine it, essentially helping iterate through the zipped list
  -- foldl requires three parameters: a function that combines the values, an accumulator (0.0), and a populated list
  -- (M.typeOfAtoms.zip M.numOfAtoms) creates a zipped list from the two lists
  -- so that each index in the zipped list is a tuple
  List.foldl (fun acc (atom, atomNum) => acc + atom.atomicMass * atomNum) 0.0 (M.typeOfAtoms.zip M.numOfAtoms)

#eval molWeight water

-- Pattern matching is done manually with "let" if using a separate function
def weight (acc : Float) (atomNumPair : Chemprop × Float) : Float :=
  let (atom, atomNum) := atomNumPair
  acc + atom.atomicMass * atomNum

def molWeight1 (M : Molecule) : Float :=
  -- Here we can use foldl without a lambda function
  List.foldl weight 0.0 (M.typeOfAtoms.zip M.numOfAtoms)

#eval molWeight1 water
