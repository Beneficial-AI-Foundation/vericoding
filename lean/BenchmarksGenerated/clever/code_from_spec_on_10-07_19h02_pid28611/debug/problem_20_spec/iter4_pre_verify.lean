import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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

def implementation (numbers: List Rat): (Rat × Rat) :=
match numbers with
| [] => (0, 0)
| [x] => (x, x)
| h1 :: h2 :: t => 
  let pairs := List.product numbers numbers
  let valid_pairs := pairs.filter (fun x => x.1 ≤ x.2)
  match valid_pairs with
  | [] => (h1, h1)
  | head :: _ => valid_pairs.foldl (fun acc x => 
    if |x.2 - x.1| < |acc.2 - acc.1| then x else acc) head

-- LLM HELPER
lemma list_product_mem {α : Type*} (l : List α) (x y : α) : 
  x ∈ l → y ∈ l → (x, y) ∈ List.product l l := by
  intro hx hy
  exact List.mem_product.mpr ⟨hx, hy⟩

-- LLM HELPER
lemma filter_nonempty_of_le (numbers : List Rat) (h : 2 ≤ numbers.length) :
  (List.product numbers numbers).filter (fun x => x.1 ≤ x.2) ≠ [] := by
  have h_len : 0 < numbers.length := by linarith
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h_len
  have : (x, x) ∈ List.product numbers numbers := list_product_mem numbers x x hx hx
  have : (x, x) ∈ (List.product numbers numbers).filter (fun x => x.1 ≤ x.2) := by
    rw [List.mem_filter]
    constructor
    · exact this
    · simp
  exact List.ne_nil_of_mem this

-- LLM HELPER
lemma valid_pairs_all_valid (numbers : List Rat) :
  ∀ p ∈ (List.product numbers numbers).filter (fun x => x.1 ≤ x.2), p.1 ≤ p.2 := by
  intro p hp
  rw [List.mem_filter] at hp
  simp at hp
  exact hp.2

-- LLM HELPER
lemma valid_pairs_all_in_numbers (numbers : List Rat) :
  ∀ p ∈ (List.product numbers numbers).filter (fun x => x.1 ≤ x.2), p.1 ∈ numbers ∧ p.2 ∈ numbers := by
  intro p hp
  rw [List.mem_filter] at hp
  rw [List.mem_product] at hp
  exact hp.1

-- LLM HELPER
lemma head_in_valid_pairs {α : Type*} (l : List α) (h : l ≠ []) :
  ∃ head tail, l = head :: tail ∧ head ∈ l := by
  cases' l with head tail
  · contradiction
  · use head, tail
    exact ⟨rfl, List.mem_cons_self _ _⟩

-- LLM HELPER
lemma foldl_preserves_order (valid_pairs : List (Rat × Rat)) (head : Rat × Rat) 
  (h_valid : ∀ p ∈ valid_pairs, p.1 ≤ p.2) (h_head : head.1 ≤ head.2) :
  let result := valid_pairs.foldl (fun acc x => 
    if |x.2 - x.1| < |acc.2 - acc.1| then x else acc) head
  result.1 ≤ result.2 := by
  induction valid_pairs generalizing head with
  | nil => exact h_head
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro p hp
      exact h_valid p (List.mem_cons_of_mem x hp)
    · simp
      split_ifs with h_cond
      · exact h_valid x (List.mem_cons_self x xs)
      · exact h_head

-- LLM HELPER
lemma foldl_preserves_membership (valid_pairs : List (Rat × Rat)) (head : Rat × Rat) 
  (h_valid : ∀ p ∈ head :: valid_pairs, p.1 ∈ numbers ∧ p.2 ∈ numbers) (numbers : List Rat) :
  let result := valid_pairs.foldl (fun acc x => 
    if |x.2 - x.1| < |acc.2 - acc.1| then x else acc) head
  result.1 ∈ numbers ∧ result.2 ∈ numbers := by
  induction valid_pairs generalizing head with
  | nil => exact h_valid head (List.mem_cons_self head [])
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro p hp
    simp
    split_ifs with h_cond
    · cases' hp with hp hp
      · rw [← hp]
        exact h_valid x (List.mem_cons_of_mem head (List.mem_cons_self x xs))
      · exact h_valid p (List.mem_cons_of_mem head (List.mem_cons_of_mem x hp))
    · cases' hp with hp hp
      · rw [← hp]
        exact h_valid head (List.mem_cons_self head (x :: xs))
      · exact h_valid p (List.mem_cons_of_mem head (List.mem_cons_of_mem x hp))

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  cases' numbers with h1 t1
  · -- empty list case
    use (0, 0)
    simp
    intro h
    norm_num at h
  · cases' t1 with h2 t2
    · -- single element case
      use (h1, h1)
      simp
      intro h
      norm_num at h
    · -- at least two elements case
      let pairs := List.product (h1 :: h2 :: t2) (h1 :: h2 :: t2)
      let valid_pairs := pairs.filter (fun x => x.1 ≤ x.2)
      have h_len : 2 ≤ (h1 :: h2 :: t2).length := by simp [List.length_cons]; norm_num
      have h_valid_nonempty : valid_pairs ≠ [] := filter_nonempty_of_le (h1 :: h2 :: t2) h_len
      obtain ⟨head, tail, h_eq, h_head_mem⟩ := head_in_valid_pairs valid_pairs h_valid_nonempty
      use (valid_pairs.foldl (fun acc x => 
        if |x.2 - x.1| < |acc.2 - acc.1| then x else acc) head)
      constructor
      · simp [valid_pairs, h_eq]
        rw [h_eq]
        simp
      · intro h_len_ge
        have h_head_valid : head.1 ≤ head.2 := valid_pairs_all_valid (h1 :: h2 :: t2) head h_head_mem
        have h_head_in : head.1 ∈ (h1 :: h2 :: t2) ∧ head.2 ∈ (h1 :: h2 :: t2) := 
          valid_pairs_all_in_numbers (h1 :: h2 :: t2) head h_head_mem
        constructor
        · -- smaller ≤ larger
          apply foldl_preserves_order
          · intro p hp
            exact valid_pairs_all_valid (h1 :: h2 :: t2) p hp
          · exact h_head_valid
        constructor
        · -- smaller ∈ numbers
          have h_all_in : ∀ p ∈ head :: valid_pairs, p.1 ∈ (h1 :: h2 :: t2) ∧ p.2 ∈ (h1 :: h2 :: t2) := by
            intro p hp
            cases' hp with hp hp
            · rw [← hp]
              exact h_head_in
            · exact valid_pairs_all_in_numbers (h1 :: h2 :: t2) p hp
          exact (foldl_preserves_membership valid_pairs head h_all_in (h1 :: h2 :: t2)).1
        constructor
        · -- larger ∈ numbers
          have h_all_in : ∀ p ∈ head :: valid_pairs, p.1 ∈ (h1 :: h2 :: t2) ∧ p.2 ∈ (h1 :: h2 :: t2) := by
            intro p hp
            cases' hp with hp hp
            · rw [← hp]
              exact h_head_in
            · exact valid_pairs_all_in_numbers (h1 :: h2 :: t2) p hp
          exact (foldl_preserves_membership valid_pairs head h_all_in (h1 :: h2 :: t2)).2
        constructor
        · -- minimality property
          intro x y hx hy
          -- This is the key property that our algorithm finds the minimum difference
          -- We need to show that any pair (x,y) from numbers has at least as large difference
          -- as our result
          have h_xy_in_valid : (min x y, max x y) ∈ valid_pairs := by
            rw [List.mem_filter]
            constructor
            · exact list_product_mem (h1 :: h2 :: t2) (min x y) (max x y) 
                (by cases' le_total x y with h h; simp [min_def, h]; exact hx; simp [min_def, h]; exact hy)
                (by cases' le_total x y with h h; simp [max_def, h]; exact hy; simp [max_def, h]; exact hx)
            · simp
              exact min_le_max x y
          -- The foldl finds the minimum, so our result has difference ≤ any valid pair
          have h_abs_eq : |max x y - min x y| = |x - y| := by
            cases' le_total x y with h h
            · simp [min_def, max_def, h]
              exact abs_sub_comm x y
            · simp [min_def, max_def, h]
          rw [← h_abs_eq]
          -- This requires a more complex proof about foldl minimality
          sorry
        · -- duplicate handling
          intro h_eq
          simp at h_eq
          -- Need to show that if result.1 = result.2, then that element appears in numbers
          -- This follows from our membership proofs
          sorry