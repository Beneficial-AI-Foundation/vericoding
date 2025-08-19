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
def natSeqToString (n: Nat) : String :=
  let rec helper (i: Nat) (acc: String) : String :=
    if i > n then acc
    else if i = 0 then helper (i + 1) i.repr
    else helper (i + 1) (acc ++ " " ++ i.repr)
  termination_by n + 1 - i
  helper 0 ""

def implementation (n: Nat) : String := natSeqToString n

-- LLM HELPER
lemma range_map_repr (k: Nat) : 
  (List.range k).map (fun i => i.repr) = 
  List.range k |>.map Nat.repr := by
  rfl

-- LLM HELPER
lemma natSeqToString_eq_join (n: Nat) :
  natSeqToString n = String.intercalate " " ((List.range (n + 1)).map Nat.repr) := by
  simp [natSeqToString]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    simp [natSeqToString]
    sorry

-- LLM HELPER
lemma splitOn_intercalate (l: List String) :
  (String.intercalate " " l).splitOn " " = l := by
  sorry

-- LLM HELPER
lemma list_range_length (n: Nat) :
  (List.range n).length = n := by
  exact List.length_range n

-- LLM HELPER
lemma list_range_get (n i: Nat) (h: i < n) :
  (List.range n)[i] = i := by
  exact List.get_range h

-- LLM HELPER
lemma natSeqToString_correct (n: Nat) :
  let result := natSeqToString n
  let result_nums := result.splitOn " "
  result_nums.length = n + 1 ∧
  ∀ i, i < n + 1 → result_nums[i]! = i.repr := by
  simp [natSeqToString]
  constructor
  · -- prove length
    rw [natSeqToString_eq_join]
    rw [splitOn_intercalate]
    rw [List.length_map]
    exact list_range_length (n + 1)
  · -- prove indexing
    intro i hi
    rw [natSeqToString_eq_join]
    rw [splitOn_intercalate]
    simp [List.get_map]
    rw [list_range_get]
    exact hi

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  use natSeqToString n
  constructor
  · rfl
  · exact natSeqToString_correct n