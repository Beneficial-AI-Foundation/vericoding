-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkAlgorithmTermination (s : String) (ranges : List (Nat × Nat)) : List Answer := sorry

/- For ranges of length 1 or 2, the algorithm always terminates -/
-- </vc-definitions>

-- <vc-theorems>
theorem singleOrPairTerminates {s : String} {start finish : Nat} :
  finish - start + 1 ≤ 2 → 
  checkAlgorithmTermination s [(start, finish)] = [Answer.YES] :=
  sorry

/- For any range, termination depends on character count distribution -/

theorem terminationCondition {s : String} {start finish : Nat} {x y z : Nat} :
  (x = y ∧ y = z) ∨
  (x = y ∧ z = y + 1) ∨
  (y = z ∧ x = y - 1) ↔
  checkAlgorithmTermination s [(start, finish)] = [Answer.YES] :=
  sorry

/- Single character ranges always terminate -/

theorem singleCharTerminates {s : String} {i : Nat} :
  i < s.length →
  checkAlgorithmTermination s [(i+1, i+1)] = [Answer.YES] :=
  sorry

/- Equal character counts lead to termination -/

theorem equalCountsTerminate {s : String} {x y z : Nat} :
  x = y ∧ y = z →
  checkAlgorithmTermination s [(1, s.length)] = [Answer.YES] :=
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval check_algorithm_termination "zyxxxxxxyyz" [(5, 5), (1, 3), (1, 11), (1, 4), (3, 6)]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval check_algorithm_termination "x" [(1, 1)]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval check_algorithm_termination "xyz" [(1, 3)]
-- </vc-theorems>