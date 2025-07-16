def problem_spec
-- function signature
(implementation: List Rat → (Rat × Rat))
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: (Rat × Rat)) :=
2 ≤ numbers.length →
(let (smaller, larger) := result;
let abs_diff := |larger - smaller|;
smaller ≤ larger ∧
smaller ∈ numbers ∧
larger ∈ numbers ∧
(∀ x y, x ∈ numbers → y ∈ numbers →  abs_diff ≤ |x - y|) ∧
(smaller = larger → 1 ≤ (numbers.filter (fun z => z = smaller)).length));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_diff_pair (numbers: List Rat): (Rat × Rat) :=
match numbers with
| [] => (0, 0)
| [x] => (x, x)
| x :: xs =>
  let pairs := List.product numbers numbers
  let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
  match valid_pairs with
  | [] => (x, x)
  | p :: ps =>
    ps.foldl (fun acc (a, b) =>
      let (curr_a, curr_b) := acc
      if |b - a| < |curr_b - curr_a| then (a, b) else acc) p

def implementation (numbers: List Rat): (Rat × Rat) := find_min_diff_pair numbers

-- LLM HELPER
lemma mem_product_iff {α β : Type*} (a : α) (b : β) (l1 : List α) (l2 : List β) :
  (a, b) ∈ List.product l1 l2 ↔ a ∈ l1 ∧ b ∈ l2 := by
  simp [List.mem_product]

-- LLM HELPER
lemma filter_nonempty_of_mem {α : Type*} (l : List α) (x : α) (h : x ∈ l) :
  (l.filter (fun y => y ≤ x)).length ≥ 1 := by
  have : x ∈ l.filter (fun y => y ≤ x) := by
    simp [List.mem_filter, h, le_refl]
  exact List.length_pos_of_mem this

-- LLM HELPER
lemma exists_pair_in_product (numbers : List Rat) (h : 2 ≤ numbers.length) :
  ∃ a b, (a, b) ∈ List.product numbers numbers ∧ a ≤ b := by
  cases' numbers with x xs
  · simp at h
  cases' xs with y ys
  · simp at h
  use x, y
  constructor
  · simp [List.product, List.mem_product]
    left
    constructor <;> simp
  · by_cases h : x ≤ y
    · exact h
    · push_neg at h
      exact le_of_lt h

-- LLM HELPER
lemma foldl_preserves_min_property (pairs : List (Rat × Rat)) (init : Rat × Rat) :
  let result := pairs.foldl (fun acc (a, b) =>
    let (curr_a, curr_b) := acc
    if |b - a| < |curr_b - curr_a| then (a, b) else acc) init
  result = init ∨ result ∈ pairs := by
  induction pairs generalizing init with
  | nil => simp
  | cons p ps ih =>
    simp [List.foldl]
    let new_acc := if |p.2 - p.1| < |init.2 - init.1| then p else init
    have h := ih new_acc
    cases h with
    | inl h => 
      if hcond : |p.2 - p.1| < |init.2 - init.1| then
        simp [hcond] at h
        right
        rw [h]
        simp
      else
        simp [hcond] at h
        left
        exact h
    | inr h => 
      right
      simp
      exact h

-- LLM HELPER
lemma valid_pairs_nonempty (numbers : List Rat) (h : 2 ≤ numbers.length) :
  let pairs := List.product numbers numbers
  let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
  valid_pairs.length ≥ 1 := by
  cases' numbers with x xs
  · simp at h
  cases' xs with y ys
  · simp at h
  have : (x, x) ∈ valid_pairs := by
    simp [valid_pairs, List.mem_filter, List.mem_product]
  exact List.length_pos_of_mem this

-- LLM HELPER
lemma foldl_result_mem_valid_pairs (numbers : List Rat) (h : 2 ≤ numbers.length) :
  let pairs := List.product numbers numbers
  let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
  ∀ p ps, valid_pairs = p :: ps →
    let result := ps.foldl (fun acc (a, b) =>
      let (curr_a, curr_b) := acc
      if |b - a| < |curr_b - curr_a| then (a, b) else acc) p
    result ∈ valid_pairs := by
  intro p ps h_eq
  have h_fold := foldl_preserves_min_property ps p
  cases h_fold with
  | inl h => 
    rw [h_eq]
    simp
  | inr h => 
    rw [h_eq]
    simp
    exact h

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use find_min_diff_pair numbers
  constructor
  · rfl
  · intro h_len
    cases' numbers with x xs
    · simp at h_len
    cases' xs with y ys
    · simp at h_len
    simp [find_min_diff_pair]
    let pairs := List.product (x :: y :: ys) (x :: y :: ys)
    let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
    have h_nonempty : valid_pairs.length ≥ 1 := valid_pairs_nonempty (x :: y :: ys) h_len
    cases' valid_pairs with p ps
    · simp at h_nonempty
    simp
    let result := ps.foldl (fun acc (a, b) =>
      let (curr_a, curr_b) := acc
      if |b - a| < |curr_b - curr_a| then (a, b) else acc) p
    have h_mem := foldl_result_mem_valid_pairs (x :: y :: ys) h_len p ps rfl
    have h_result_in_valid : result ∈ valid_pairs := h_mem
    have h_valid_in_pairs : ∀ ab, ab ∈ valid_pairs → ab ∈ pairs := fun ab hab => 
      List.mem_of_mem_filter hab
    have h_result_in_pairs : result ∈ pairs := h_valid_in_pairs result h_result_in_valid
    have h_result_ordered : result.1 ≤ result.2 := by
      simp [List.mem_filter] at h_result_in_valid
      exact h_result_in_valid.2
    have h_result_components : result.1 ∈ (x :: y :: ys) ∧ result.2 ∈ (x :: y :: ys) := by
      simp [List.mem_product] at h_result_in_pairs
      exact h_result_in_pairs
    constructor
    · exact h_result_ordered
    constructor
    · exact h_result_components.1
    constructor
    · exact h_result_components.2
    constructor
    · intro a b ha hb
      simp [abs_sub_comm]
      have : (a, b) ∈ pairs ∨ (b, a) ∈ pairs := by
        simp [pairs, List.mem_product]
        exact ⟨ha, hb⟩
      by_cases h : a ≤ b
      · have hab_in_valid : (a, b) ∈ valid_pairs := by
          simp [valid_pairs, List.mem_filter, List.mem_product]
          exact ⟨ha, hb, h⟩
        have : |result.2 - result.1| ≤ |b - a| := by
          by_contra h_not
          push_neg at h_not
          have : |b - a| < |result.2 - result.1| := h_not
          rw [abs_sub_comm] at this
          have : |a - b| < |result.2 - result.1| := this
          simp
        rw [abs_sub_comm]
        exact this
      · push_neg at h
        have hba_in_valid : (b, a) ∈ valid_pairs := by
          simp [valid_pairs, List.mem_filter, List.mem_product]
          exact ⟨hb, ha, le_of_lt h⟩
        have : |result.2 - result.1| ≤ |a - b| := by
          by_contra h_not
          push_neg at h_not
          have : |a - b| < |result.2 - result.1| := h_not
          simp
        exact this
    · intro h_eq
      rw [h_eq]
      have : result.1 ∈ (x :: y :: ys) := h_result_components.1
      have count_ge_one : ((x :: y :: ys).filter (fun z => z = result.1)).length ≥ 1 := by
        have : result.1 ∈ (x :: y :: ys).filter (fun z => z = result.1) := by
          simp [List.mem_filter, this]
        exact List.length_pos_of_mem this
      exact count_ge_one