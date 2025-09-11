-- <vc-preamble>
def commas (n : Float) : String := sorry

def String.toFloat! (s : String) : Float := sorry
instance : ToString Int where toString := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Int.abs (n : Int) : Int := if n < 0 then -n else n

theorem integers_format_correctly (n : Int) 
  (h : -999999999999999 ≤ n ∧ n ≤ 999999999999999) :
  let result : String := commas (Float.ofInt n);
  (Int.abs n ≥ 1000 → result.contains ',' ) ∧ 
  (¬result.contains '.') ∧
  ((result.replace "," "").toInt? = some n) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem floats_format_correctly (n : Float)
  (h1 : ¬n.isNaN)
  (h2 : ¬n.isInf) 
  (h3 : -1e10 ≤ n ∧ n ≤ 1e10) :
  let result : String := commas n;
  (result.contains '.' → (result.splitOn "." |>.get! 1).length ≤ 3) ∧
  Float.abs ((result.replace "," "").toFloat! - n) < 1e-2 := sorry

theorem zero_cases :
  commas 0 = "0" ∧ commas (-0.0) = "0" := sorry

/-
info: '1,000'
-/
-- #guard_msgs in
-- #eval commas 1000

/-
info: '100.235'
-/
-- #guard_msgs in
-- #eval commas 100.2346

/-
info: '-1,000,000.123'
-/
-- #guard_msgs in
-- #eval commas -1000000.123
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded