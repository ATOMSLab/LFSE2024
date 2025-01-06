def get_input : IO String := do
  let stdin ← IO.getStdin
  stdin.getLine

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def factorialm (n : Nat) : Nat :=
  match n with
    | 0 => 1
    | n + 1 => (n + 1) * factorialm n

example : factorial = factorialm := by rfl

def main : IO Unit := do
 IO.println "Enter number:"
 let num ← get_input
 match num.trim.toNat? with
  | some num =>
    let fact := factorial (num)
    IO.println s!"Factorial: {fact}"
  | none => IO.println "Invalid entry. Please enter a valid natural number."


-- What's going on with String.toNat? ? This has type Option Nat
