-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lineup_students (input : String) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lineupStudentsLengthPreserved (input : String) (names : List String) :
  names = lineup_students input →
  (lineup_students input).length = names.length :=
sorry

theorem lineupStudentsSorted {result : List String} (i : Nat) (h : i + 1 < result.length) :
  let a := result[i]!
  let b := result[i+1]!
  (a.length = b.length → a ≥ b) ∧
  (a.length ≠ b.length → a.length > b.length) :=
sorry

theorem lineupStudentsPreservesElements (input : String) (names : List String) :
  names = lineup_students input →
  ∀ x, (x ∈ names ↔ x ∈ lineup_students input) :=
sorry

theorem lineupStudentsSingleElement (name : String) :
  lineup_students name = [name] :=
sorry

theorem lineupStudentsEmpty :
  lineup_students "" = [] :=
sorry
-- </vc-theorems>