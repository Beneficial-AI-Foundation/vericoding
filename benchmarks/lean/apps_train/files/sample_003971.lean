/-
You will be given two ASCII strings, `a` and `b`. Your task is write a function to determine which one of these strings is "worth" more, and return it.

A string's worth is determined by the sum of its ASCII codepoint indexes. So, for example, the string `HELLO` has a value of 372: H is codepoint 72, E 69, L 76, and O is 79. The sum of these values is 372.

In the event of a tie, you should return the first string, i.e. `a`.
-/

def String.sumAscii (s : String) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def highest_value (a b : String) : String :=
sorry

theorem highest_value_is_input (a b : String) :
  let result := highest_value a b
  result = a ∨ result = b := sorry

theorem highest_value_maximizes_sum (a b : String) :
  let result := highest_value a b
  String.sumAscii result ≥ String.sumAscii (if result = a then b else a) := sorry

theorem highest_value_equal_sums (a b : String) :
  String.sumAscii a = String.sumAscii b →
  highest_value a b = a := sorry

theorem highest_value_identical (s : String) :
  highest_value s s = s := sorry

theorem highest_value_nonempty (a b : String) :
  a.length > 0 →
  b.length > 0 →
  (highest_value a b).length > 0 := sorry

/-
info: 'KkLlMmNnOoPp4567'
-/
-- #guard_msgs in
-- #eval highest_value "AaBbCcXxYyZz0189" "KkLlMmNnOoPp4567"

/-
info: 'ABcd'
-/
-- #guard_msgs in
-- #eval highest_value "ABcd" "0123"

/-
info: "{}[]@~'#:;"
-/
-- #guard_msgs in
-- #eval highest_value "!"?$%^&*()" "{}[]@~"#:;"

-- Apps difficulty: introductory
-- Assurance level: unguarded