def main : IO Unit := do
  let stdin ← IO.getStdin

  IO.println "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace
  IO.println s!"Hello, {name}!"
