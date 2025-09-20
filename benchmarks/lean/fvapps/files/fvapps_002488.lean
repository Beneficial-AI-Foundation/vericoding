-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def student_union (n1 : Nat) (eng : String) (n2 : Nat) (fre : String) : Nat :=
sorry

def stringToList (s : String) : List Int :=
sorry

def removeDuplicates (l : List Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem student_union_leq_sum_lengths {n1 n2 : Nat} {eng fre : String} :
  student_union n1 eng n2 fre ≤ n1 + n2 :=
sorry

theorem student_union_equals_union_length {n1 n2 : Nat} {eng fre : String} :
  ∃ l1 l2 : List Int,
    l1 = stringToList eng ∧
    l2 = stringToList fre ∧
    student_union n1 eng n2 fre = (removeDuplicates (l1 ++ l2)).length :=
sorry

theorem student_union_identical_lists {n : Nat} {nums : String} :
  student_union n nums n nums = (removeDuplicates (stringToList nums)).length :=
sorry
-- </vc-theorems>