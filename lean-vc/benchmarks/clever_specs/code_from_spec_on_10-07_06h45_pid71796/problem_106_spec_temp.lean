-- LLM HELPER
def Nat.Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def Nat.Odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

-- LLM HELPER
def Nat.factorial : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * Nat.factorial n

def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  (result.length = n) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Nat.Even i) → (result[i-1]?.getD 0 = Nat.factorial i)) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Nat.Odd i) → (result[i-1]?.getD 0 = (List.range (i+1)).sum))
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def compute_element (i: Nat) : Int :=
  if Nat.Even i then (Nat.factorial i : Int) else ((List.range (i+1)).sum : Int)

-- LLM HELPER
def build_list (n: Int) : List Int :=
  if n ≤ 0 then []
  else (List.range n.natAbs).map (fun i => compute_element (i+1))

def implementation (n: Int) : List Int := build_list n

-- LLM HELPER
lemma build_list_length (n: Int) : (build_list n).length = n := by
  simp [build_list]
  split_ifs with h
  · simp
    omega
  · simp [List.length_map, List.length_range]
    exact Int.natAbs_of_nonneg (le_of_not_le h)

-- LLM HELPER
lemma build_list_even_element (n: Int) (i: Nat) (h1: 1 ≤ i) (h2: ↑i ≤ n) (h3: Nat.Even i) : 
  (build_list n)[i-1]?.getD 0 = (Nat.factorial i : Int) := by
  simp [build_list]
  split_ifs with h
  · omega
  · simp [List.get?_map, List.get?_range, compute_element]
    rw [if_pos h3]
    simp
    constructor
    · omega
    · rw [Int.natAbs_of_nonneg (le_of_not_le h)]
      omega

-- LLM HELPER
lemma build_list_odd_element (n: Int) (i: Nat) (h1: 1 ≤ i) (h2: ↑i ≤ n) (h3: Nat.Odd i) : 
  (build_list n)[i-1]?.getD 0 = ((List.range (i+1)).sum : Int) := by
  simp [build_list]
  split_ifs with h
  · omega
  · simp [List.get?_map, List.get?_range, compute_element]
    rw [if_neg (fun h_even => by
      cases h3 with
      | intro k hk =>
        cases h_even with
        | intro j hj =>
          rw [hk, hj]
          simp
          omega)]
    simp
    constructor
    · omega
    · rw [Int.natAbs_of_nonneg (le_of_not_le h)]
      omega

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use build_list n
  constructor
  · rfl
  · constructor
    · exact build_list_length n
    · constructor
      · intros i h1 h2 h3
        exact build_list_even_element n i h1 h2 h3
      · intros i h1 h2 h3
        exact build_list_odd_element n i h1 h2 h3