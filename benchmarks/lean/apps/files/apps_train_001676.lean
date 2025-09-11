-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (expr : String) : String := sorry

theorem basic_operations 
  (x y : Float) (op : Char) 
  (h1 : 0.1 ≤ x ∧ x ≤ 100)
  (h2 : 0.1 ≤ y ∧ y ≤ 100) 
  (h3 : op = '+' ∨ op = '-' ∨ op = '*' ∨ op = '$') :
  let expr := toString x ++ toString op ++ toString y
  let result := calculate expr
  match op with
  | '+' => result = toString (x + y)
  | '-' => result = toString (x - y) 
  | '*' => result = toString (x * y)
  | '$' => result = toString (x / y)
  | _ => False
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_chars
  (s : String)
  (h : ∀ c ∈ s.data, c ∉ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '-', '*', '$', '.']) :
  calculate (String.append "1" (String.append s "1")) = "400: Bad request" := sorry

theorem simple_cases :
  calculate "0" = "0.0" ∧
  calculate "1.5*2" = "3.0" ∧
  calculate "10+5" = "15.0" ∧
  calculate "10-5" = "5.0" := sorry

/-
info: '2.0'
-/
-- #guard_msgs in
-- #eval calculate "1+1"

/-
info: '5.0'
-/
-- #guard_msgs in
-- #eval calculate "10$2"

/-
info: '4.5'
-/
-- #guard_msgs in
-- #eval calculate "1.5*3"

/-
info: '81.0'
-/
-- #guard_msgs in
-- #eval calculate "1000$2.5$5+5-5+6$6"

/-
info: '400: Bad request'
-/
-- #guard_msgs in
-- #eval calculate "10-9p"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded