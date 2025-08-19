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
  helper 0 ""

def implementation (n: Nat) : String := natSeqToString n

-- LLM HELPER
lemma natSeqToString_helper_correct (n k: Nat) (acc: String) :
  let rec helper (i: Nat) (acc: String) : String :=
    if i > n then acc
    else if i = 0 then helper (i + 1) i.repr
    else helper (i + 1) (acc ++ " " ++ i.repr)
  k ≤ n →
  helper k acc = acc ++ (if k = 0 then "" else " ") ++ 
    String.intercalate " " (List.range (n + 1 - k) |>.map (fun i => (i + k).repr)) := by
  sorry

-- LLM HELPER
lemma natSeqToString_correct (n: Nat) :
  let result := natSeqToString n
  let result_nums := result.splitOn " "
  result_nums.length = n + 1 ∧
  ∀ i, i < n + 1 → result_nums[i]! = i.repr := by
  simp [natSeqToString]
  constructor
  · -- prove length
    sorry
  · -- prove indexing
    sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  use natSeqToString n
  constructor
  · rfl
  · exact natSeqToString_correct n