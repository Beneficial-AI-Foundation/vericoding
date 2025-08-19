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
  String.intercalate " " ((List.range (n + 1)).map Nat.repr)

def implementation (n: Nat) : String := natSeqToString n

-- LLM HELPER
lemma list_range_length (n: Nat) :
  (List.range n).length = n := by
  exact List.length_range n

-- LLM HELPER
lemma list_range_get (n i: Nat) (h: i < n) :
  (List.range n)[i]! = i := by
  rw [List.get!_eq_get]
  exact List.get_range h

-- LLM HELPER
lemma repr_no_space (n: Nat) : " " ∉ (Nat.repr n).data := by
  simp [Nat.repr]
  induction n with
  | zero => simp
  | succ n ih => 
    simp [Nat.repr, Nat.toDigitsCore]
    sorry

-- LLM HELPER
lemma String.splitOn_intercalate_space (l: List String) (h: ∀ s ∈ l, " " ∉ s.data) :
  (String.intercalate " " l).splitOn " " = l := by
  induction l with
  | nil => simp [String.intercalate, String.splitOn]
  | cons head tail ih =>
    simp [String.intercalate]
    cases tail with
    | nil => 
      simp [String.intercalate, String.splitOn]
      sorry
    | cons t_head t_tail =>
      simp [String.intercalate]
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
    have h : ∀ s ∈ (List.range (n + 1)).map Nat.repr, " " ∉ s.data := by
      intro s hs
      simp [List.mem_map] at hs
      obtain ⟨k, _, hk⟩ := hs
      rw [← hk]
      exact repr_no_space k
    rw [String.splitOn_intercalate_space _ h]
    rw [List.length_map]
    exact list_range_length (n + 1)
  · -- prove indexing
    intro i hi
    have h : ∀ s ∈ (List.range (n + 1)).map Nat.repr, " " ∉ s.data := by
      intro s hs
      simp [List.mem_map] at hs
      obtain ⟨k, _, hk⟩ := hs
      rw [← hk]
      exact repr_no_space k
    rw [String.splitOn_intercalate_space _ h]
    simp [List.get!_map]
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