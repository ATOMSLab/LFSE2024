/- Strings! -/

-- Define a string with double quotes
def string_example := "hello"
-- Single quotes are used for characters
def char_example   := 'c'
-- string to list
#eval string_example.toList
--list of char to joined string
#eval ['h','e','l','l','o'].asString
-- list of strings to string
#eval string_example.endsWith "o"
#eval "hello    ".trim
#eval string_example.toUpper
-- string concantenation methods
#eval string_example ++ " everyone"
-- passing values into strings
#eval s!"{string_example} everyone"
-- Reverse a string (example of chaining string methods)
#eval string_example.toList.reverse.asString
def string_example2 :="12"
-- number parsing
#eval string_example2.toNat!
#eval string_example2.toInt!

def float_parsing (str:String) :=
  let parts := str.split (· == '.')
  match parts with
  | [intPart, fracPart] =>
    let fullnum :=(intPart++fracPart).toNat!
    let plc:=fracPart
    some (Float.ofScientific fullnum true plc.length)
  | _ => none


#eval float_parsing "12.532"
