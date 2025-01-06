-- Here's how Option works:
def safeDivide (a b : Nat) : Option Nat :=
  if b == 0 then
    none
  else
    some (a / b)

def main : IO Unit := do
  let result1 := safeDivide 10 2
  let result2 := safeDivide 10 0
  IO.println s!"10 / 2 = {result1}"
  IO.println s!"10 / 0 = {result2}"
