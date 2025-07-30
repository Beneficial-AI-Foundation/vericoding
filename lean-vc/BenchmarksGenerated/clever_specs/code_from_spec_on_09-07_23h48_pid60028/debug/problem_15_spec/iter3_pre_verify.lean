def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(n: Nat) :=
-- spec
let spec (result: String) :=
let result_nums := result.splitOn " ";
result_nums.length = n + 1 ∧
∀ i, i < n + 1 → result_nums[i]! = i.repr;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def nat_list_to_string (lst: List Nat) : String :=
  String.intercalate " " (lst.map Nat.repr)

-- LLM HELPER
def range_list (n: Nat) : List Nat :=
  List.range (n + 1)

def implementation (n: Nat) : String := 
  nat_list_to_string (range_list n)

-- LLM HELPER
lemma range_list_length (n: Nat) : (range_list n).length = n + 1 := by
  simp [range_list, List.length_range]

-- LLM HELPER
lemma range_list_get (n: Nat) (i: Nat) (h: i < n + 1) : (range_list n)[i]! = i := by
  simp [range_list]
  rw [List.getElem!_eq_getElem]
  exact List.getElem_range h

-- LLM HELPER
lemma nat_list_to_string_split (lst: List Nat) : 
  (nat_list_to_string lst).splitOn " " = lst.map Nat.repr := by
  simp [nat_list_to_string]
  exact String.splitOn_intercalate_of_not_mem (by simp)

-- LLM HELPER
lemma implementation_spec (n: Nat) : 
  let result := implementation n
  let result_nums := result.splitOn " "
  result_nums.length = n + 1 ∧ ∀ i, i < n + 1 → result_nums[i]! = i.repr := by
  simp [implementation]
  constructor
  · simp [nat_list_to_string, range_list]
    rw [String.splitOn_intercalate_of_not_mem (by simp)]
    simp [List.length_map, List.length_range]
  · intro i hi
    simp [nat_list_to_string, range_list]
    rw [String.splitOn_intercalate_of_not_mem (by simp)]
    simp [List.getElem!_map, List.getElem!_range]

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  use implementation n
  constructor
  · rfl
  · exact implementation_spec n