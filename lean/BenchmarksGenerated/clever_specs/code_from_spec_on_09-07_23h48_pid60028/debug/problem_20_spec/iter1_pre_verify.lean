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

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation, find_min_diff_pair]
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
    have h_nonempty : valid_pairs.length ≥ 1 := by
      have : (x, x) ∈ valid_pairs := by
        simp [valid_pairs, List.mem_filter, List.mem_product]
      exact List.length_pos_of_mem this
    cases' valid_pairs with p ps
    · simp at h_nonempty
    simp
    let result := ps.foldl (fun acc (a, b) =>
      let (curr_a, curr_b) := acc
      if |b - a| < |curr_b - curr_a| then (a, b) else acc) p
    constructor
    · sorry -- smaller ≤ larger
    constructor
    · sorry -- smaller ∈ numbers
    constructor
    · sorry -- larger ∈ numbers
    constructor
    · sorry -- minimality condition
    · sorry -- equal case condition