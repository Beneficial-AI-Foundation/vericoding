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
lemma splitOn_intercalate (l: List String) (h: ∀ s ∈ l, " " ∉ s.data) :
  (String.intercalate " " l).splitOn " " = l := by
  induction l with
  | nil => simp [String.intercalate, String.splitOn]
  | cons head tail ih =>
    simp [String.intercalate]
    cases tail with
    | nil => 
      simp [String.splitOn]
      have : " " ∉ head.data := h head (List.mem_cons_self head [])
      simp [String.splitOn_single this]
    | cons t_head t_tail =>
      simp [String.splitOn]
      have h1 : " " ∉ head.data := h head (List.mem_cons_self head (t_head :: t_tail))
      have h2 : ∀ s ∈ (t_head :: t_tail), " " ∉ s.data := fun s hs => h s (List.mem_cons_of_mem head hs)
      rw [ih h2]
      simp [String.splitOn_cons h1]

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
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    if h : n < 10 then
      simp [Nat.repr_aux]
      cases n with
      | zero => simp
      | succ n' =>
        if h' : n' < 9 then
          simp [Nat.repr_aux]
          cases n' <;> simp
        else
          simp [Nat.repr_aux]
    else
      simp [Nat.repr_aux]
      exact ih (n / 10) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero (fun h => by simp [h] at h; exact Nat.not_lt_zero 10 h)) (by norm_num))

-- LLM HELPER
lemma String.splitOn_single (s : String) (h : " " ∉ s.data) : s.splitOn " " = [s] := by
  simp [String.splitOn]
  sorry

-- LLM HELPER
lemma String.splitOn_cons (s : String) (h : " " ∉ s.data) : 
  ∀ rest : String, (s ++ " " ++ rest).splitOn " " = s :: rest.splitOn " " := by
  intro rest
  simp [String.splitOn]
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
    rw [splitOn_intercalate _ h]
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
    rw [splitOn_intercalate _ h]
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