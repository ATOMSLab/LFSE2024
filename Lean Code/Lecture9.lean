import Mathlib

-- Lists
def data1 : List Nat := [1, 2, 3, 4, 5, 6, 7]
def data2 : List Nat := [7, 8, 1, 2, 3, 4]

-- Getting the length of a list
--#eval List.length data1

-- Accessing an element in a list
--#eval data1[3]

-- Accessing the last element in a list
--#eval List.tail data1

-- Accessing the first element in a list
--#eval List.head! data1

-- Slicing a sublist from a list - no built-in function yet, so write one!
def sliceList {α : Type} (l : List α) (start end1 : Nat) : List α :=
  l.drop start |>.take (end1 - start)

#eval sliceList data1 0 4

def checknum (x : Nat) : Bool := x > 4
#eval List.filter checknum data1

-- Or, with an anonymous function
#eval List.filter (λ x => x > 4) data1
-- Alternatively
#eval List.filter (fun x => x > 4) data1


-- Example usage:
#eval sliceList [0, 1, 2, 3, 4, 5] 2 5

-- Summing elements in a list
def sum_list : List Nat → Nat
  | [] => 0
  | (x :: xs) => x + sum_list xs
-- This is not tail recursive

-- Apply "square" operation to every element in a list
def square_list : List Nat → List Nat
  | [] => []
  | (x :: xs) => (x * x) :: square_list xs

def sum_squares_list : List Nat →  Nat
  | [] => 0
  | (x :: xs) => (x * x) + sum_squares_list xs


--def sum_listfoldl (x : List Nat): List Nat → Nat :=
--  List.foldl x

def square_difference : List Nat → List Nat → List Nat
  | [], [] => []
  | (x1 :: x1s), (x2 :: x2s) => (x2 - x1)^2 :: square_difference x1s x2s
  | _, _ => []

def SE (L1 L2 : List Nat) : Nat := sum_squares_list (square_difference L1 L2)

#eval SE data1 data2


def matrix1 : List (List Nat) := [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

 -- List of string
def dataTypes : List String := ["oscar", "boolean", "float", "true", "false"]


def filterTheList (minLength : Nat) : List String :=
  dataTypes.filter (λ e => e.length > minLength)

def filterIt : IO Unit := do
  let filteredStrings := filterTheList 5
  IO.println ""
  for str in filteredStrings do
    IO.println str

#eval filterIt


#eval data1

def Vector (α : Type ) (n : ℕ) :=
  { l : List α // l.length = n }

-- Function to sum elements in a Vector of natural numbers
def sumVector (n : ℕ) (v : Vector ℕ n) : ℕ :=
  v.val.sum

def exampleVector : Vector ℕ 3 :=
  ⟨[1, 2, 3], rfl⟩

#eval sumVector 3 exampleVector

def exampleVector2 : Vector ℕ 3 :=
  ⟨[3, 2, 1], rfl⟩
