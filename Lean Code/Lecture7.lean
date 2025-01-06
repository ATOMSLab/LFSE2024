/- We don't need to import Mathlib for this class!
But Lean only knows that the ℕ character correspond to the Nat type
if it has Mathlib, so our functions need to use Nat instead of ℕ
-/

-- Define a floating point number a:
def a : Float := 50.0
-- Lean won't let you replace it with a new value!
-- def a : Float := a + 10
-- You need to define something new
def b : Float := a + 10
#eval b


-- Function with pattern-matching
def element : Nat → String
  | 0 => "Not an element"
  | 1 => "Hydrogen"
  | 2 => "Helium"
  | _ => "Not an element"

def factorial : Nat  → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

def funct2 : Nat  → Nat
  | 0 => 1
  | n+2 => n
  | 1 => 5

#eval funct2 5

--partial def not_factorial : Nat → Nat
--  | 0 => 1
--  | n + 1 => (n + 1) * not_factorial (n+1)

/- Example from FPIL 1.4 -/

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin.x

#eval origin.y

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

-- Items in a structure can share a name with items in another structure
structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- How to update a field in a structure?

-- Not the best option: transfer data into new structure
--def zeroX (p : Point) : Point :=
--  { x := 0, y := p.y }

def zeroX (p : Point) : Point :=
  { p with x := 0 }

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

#eval fourAndThree

#eval zeroX fourAndThree

-- Notice that applying the function to fourAndThree didn't change it
#eval fourAndThree


/-
Let's define some structures for chemical properties
-/


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

-- Function for calculating molecular weight (details next time!)
def molWeight (M : Molecule) : Float :=
  List.foldl (fun acc (atom, atomNum) => acc + atom.atomicMass * atomNum) 0.0 (M.typeOfAtoms.zip M.numOfAtoms)

#eval molWeight water

--import Mathlib
