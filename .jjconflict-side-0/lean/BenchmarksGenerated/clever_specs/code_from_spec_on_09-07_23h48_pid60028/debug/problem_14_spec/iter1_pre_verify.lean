def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(string: String) :=
-- spec
let spec (result: List String) :=
result.length = string.length ∧
∀ i, i < result.length →
result[i]! = string.take (i + 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def implementation (string: String) : List String :=
  let rec aux (s: String) (acc: List String) : List String :=
    if s.length = 0 then acc
    else aux s.drop(1) (acc ++ [s.take(acc.length + 1)])
  aux string []

-- LLM HELPER
lemma aux_length (s: String) (acc: List String) : 
  (let rec aux (s: String) (acc: List String) : List String :=
    if s.length = 0 then acc
    else aux s.drop(1) (acc ++ [s.take(acc.length + 1)])
   aux s acc).length = s.length + acc.length := by
  sorry

-- LLM HELPER
lemma aux_indexing (s: String) (acc: List String) (i: Nat) 
  (h: i < s.length + acc.length) :
  let result := (let rec aux (s: String) (acc: List String) : List String :=
    if s.length = 0 then acc
    else aux s.drop(1) (acc ++ [s.take(acc.length + 1)])
   aux s acc)
  if i < acc.length then
    result[i]! = acc[i]!
  else
    result[i]! = (s ++ String.mk (List.replicate acc.length ' ')).take (i + 1) := by
  sorry

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec implementation
  simp
  constructor
  · exact aux_length string []
  · intro i hi
    have h_aux := aux_indexing string [] i
    simp at h_aux
    rw [aux_length] at hi
    simp at hi
    exact h_aux hi