-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def owl_pic (s : String) : String := sorry

def containsSubstr (s : String) (sub : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem owl_pic_result_structure (s : String) :
  let result := owl_pic s
  let parts := result.splitOn "''0v0''"
  parts.length = 2 ∧ 
  parts[0]! = String.join (parts[1]!.data.reverse.map toString) := sorry

theorem owl_pic_uppercase (s : String) :
  let result := owl_pic s
  let leftSide := (result.splitOn "''0v0''")[0]!
  leftSide.toUpper = leftSide := sorry

/-
info: "XW''0v0''WX"
-/
-- #guard_msgs in
-- #eval owl_pic "xwe"

/-
info: "UAW8Y8T''0v0''T8Y8WAU"
-/
-- #guard_msgs in
-- #eval owl_pic "kuawd6r8q27y87t93r76352475437"

/-
info: "XWWXO''0v0''OXWWX"
-/
-- #guard_msgs in
-- #eval owl_pic "xweWXo"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible