def problem_spec
-- function signature
(implementation: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result : List String) :=
  lst.all (fun s => s.data.all (fun c => c.isDigit)) →
  (result.length = 0 ↔ lst.length = 0) ∧
  (result.length > 0 →
  let num_odd_digits := (lst.head!.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
  result.head! = "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
  ∧ result.tail! = implementation lst.tail!)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def count_odd_digits (s : String) : Nat :=
  (s.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length

-- LLM HELPER
def format_message (count : Nat) : String :=
  "the number of odd elements " ++ count.repr ++ "n the str" ++ count.repr ++ "ng " ++ count.repr ++ " of the " ++ count.repr ++ "nput."

def implementation (lst: List String) : List String := 
  match lst with
  | [] => []
  | h :: t => 
    let count := count_odd_digits h
    format_message count :: implementation t

-- LLM HELPER
lemma implementation_length (lst : List String) : (implementation lst).length = lst.length := by
  induction lst with
  | nil => simp [implementation]
  | cons h t ih => simp [implementation, ih]

-- LLM HELPER
lemma implementation_nonempty_iff (lst : List String) : (implementation lst).length > 0 ↔ lst.length > 0 := by
  rw [implementation_length]

-- LLM HELPER
lemma implementation_empty_iff (lst : List String) : (implementation lst).length = 0 ↔ lst.length = 0 := by
  rw [implementation_length]

-- LLM HELPER
lemma implementation_head_tail (h : String) (t : List String) : 
  implementation (h :: t) = format_message (count_odd_digits h) :: implementation t := by
  simp [implementation]

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h_all_digit
    constructor
    · exact implementation_empty_iff lst
    · intro h_len_pos
      cases' lst with h t
      · simp [implementation] at h_len_pos
      · simp [implementation_head_tail, count_odd_digits, format_message]
        constructor
        · rfl
        · rfl