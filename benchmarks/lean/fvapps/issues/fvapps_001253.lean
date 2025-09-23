-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_relation (a b : Int) : RelationType := sorry

def solve_multiple_testcases (cases : List (Int × Int)) : List RelationType := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_relation_valid (a b : Int) :
  let r := check_relation a b
  match r with
  | RelationType.less => a < b
  | RelationType.greater => a > b
  | RelationType.equal => a = b
  := sorry

theorem check_relation_total (a b : Int) :
  let r := check_relation a b
  (r = RelationType.less ∨ r = RelationType.greater ∨ r = RelationType.equal)
  := sorry

theorem solve_multiple_testcases_valid (cases : List (Int × Int)) :
  let results := solve_multiple_testcases cases
  (results.length = cases.length) ∧
  (∀ i : Nat, i < results.length → 
    results[i]! = check_relation cases[i]!.1 cases[i]!.2)
  := sorry

theorem check_relation_transitive (a b c : Int) :
  (check_relation a b = RelationType.less ∧ check_relation b c = RelationType.less 
    → check_relation a c = RelationType.less) ∧
  (check_relation a b = RelationType.greater ∧ check_relation b c = RelationType.greater
    → check_relation a c = RelationType.greater)
  := sorry

/-
info: ['<', '>', '=']
-/
-- #guard_msgs in
-- #eval solve_multiple_testcases [(10, 20), (20, 10), (10, 10)]

/-
info: ['<']
-/
-- #guard_msgs in
-- #eval solve_multiple_testcases [(5, 7)]

/-
info: ['=']
-/
-- #guard_msgs in
-- #eval solve_multiple_testcases [(1000000000, 1000000000)]
-- </vc-theorems>