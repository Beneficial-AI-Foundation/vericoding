def problem_spec
-- function signature
(implementation: String → List String)
-- inputs
(string: String) :=
-- spec
let spec (result: List String) :=
result.length = string.length ∧
∀ i, i < result.length →
result[i]! = string.take (i + 1)
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : List String :=
  let rec aux (n: Nat) (acc: List String) : List String :=
    if n = 0 then acc
    else aux (n - 1) (acc ++ [string.take (acc.length + 1)])
  aux string.length []

-- LLM HELPER
lemma aux_length (n: Nat) (acc: List String) (s: String) : 
  (let rec aux (n: Nat) (acc: List String) : List String :=
    if n = 0 then acc
    else aux (n - 1) (acc ++ [s.take (acc.length + 1)])
   aux n acc).length = n + acc.length := by
  induction n using Nat.strong_induction_on generalizing acc
  case h n ih =>
    simp only [aux]
    split
    · simp
    · rename_i h
      rw [ih (n - 1) (by omega) (acc ++ [s.take (acc.length + 1)])]
      simp
      omega

-- LLM HELPER
lemma aux_indexing (n: Nat) (acc: List String) (s: String) (i: Nat) 
  (h: i < n + acc.length) :
  let result := (let rec aux (n: Nat) (acc: List String) : List String :=
    if n = 0 then acc
    else aux (n - 1) (acc ++ [s.take (acc.length + 1)])
   aux n acc)
  if i < acc.length then
    result[i]! = acc[i]!
  else
    result[i]! = s.take (i - acc.length + 1) := by
  induction n using Nat.strong_induction_on generalizing acc
  case h n ih =>
    simp only [aux]
    split
    · rename_i h_n
      simp at h_n
      rw [h_n] at h
      simp at h
      split
      · simp
      · omega
    · rename_i h_n
      rw [ih (n - 1) (by omega) (acc ++ [s.take (acc.length + 1)])]
      · split
        · rename_i h_i
          simp
          split
          · simp [List.getElem_append_left]
          · omega
        · rename_i h_i
          simp
          split
          · rename_i h_i2
            simp at h_i2
            omega
          · simp [List.getElem_append_right]
            congr 1
            omega
      · simp
        omega

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec implementation
  simp
  constructor
  · exact aux_length string.length [] string
  · intro i hi
    have h_aux := aux_indexing string.length [] string i
    simp at h_aux
    have h_length := aux_length string.length [] string
    simp at h_length
    rw [← h_length] at hi
    have h_result := h_aux hi
    split at h_result
    · simp at *
    · simp at h_result
      exact h_result