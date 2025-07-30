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

-- LLM HELPER
def find_min_diff_pair (numbers: List Rat): (Rat × Rat) :=
match numbers with
| [] => (0, 0)
| [x] => (x, x)
| h1 :: h2 :: t => 
  let pairs := List.product numbers numbers
  let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
  match valid_pairs with
  | [] => (h1, h1)
  | head :: _ => valid_pairs.foldl (fun acc (a, b) => 
    if |b - a| < |acc.2 - acc.1| then (a, b) else acc) head

def implementation (numbers: List Rat): (Rat × Rat) := find_min_diff_pair numbers

-- LLM HELPER
lemma list_product_mem {α : Type*} (l : List α) (x y : α) : 
  x ∈ l → y ∈ l → (x, y) ∈ List.product l l := by
  intro hx hy
  exact List.mem_product.mpr ⟨hx, hy⟩

-- LLM HELPER
lemma filter_nonempty_of_le (numbers : List Rat) (h : 2 ≤ numbers.length) :
  (List.product numbers numbers).filter (fun (a, b) => a ≤ b) ≠ [] := by
  have h_len : 0 < numbers.length := by linarith
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h_len
  have : (x, x) ∈ List.product numbers numbers := list_product_mem numbers x x hx hx
  have : (x, x) ∈ (List.product numbers numbers).filter (fun (a, b) => a ≤ b) := by
    rw [List.mem_filter]
    exact ⟨this, le_refl x⟩
  exact List.ne_nil_of_mem this

-- LLM HELPER
lemma foldl_preserves_property {α β : Type*} (f : α → β → α) (init : α) (l : List β) 
  (P : α → Prop) (h_init : P init) (h_preserve : ∀ a b, P a → P (f a b)) :
  P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h_init
  | cons head tail ih =>
    apply ih
    exact h_preserve init head h_init

-- LLM HELPER
lemma valid_pairs_all_valid (numbers : List Rat) :
  ∀ p ∈ (List.product numbers numbers).filter (fun (a, b) => a ≤ b), p.1 ≤ p.2 := by
  intro p hp
  rw [List.mem_filter] at hp
  exact hp.2

-- LLM HELPER
lemma valid_pairs_all_in_numbers (numbers : List Rat) :
  ∀ p ∈ (List.product numbers numbers).filter (fun (a, b) => a ≤ b), p.1 ∈ numbers ∧ p.2 ∈ numbers := by
  intro p hp
  rw [List.mem_filter] at hp
  rw [List.mem_product] at hp
  exact hp.1

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation find_min_diff_pair
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
      let valid_pairs := pairs.filter (fun (a, b) => a ≤ b)
      have h_len : 2 ≤ (h1 :: h2 :: t2).length := by simp [List.length_cons]; norm_num
      have h_valid_nonempty : valid_pairs ≠ [] := filter_nonempty_of_le (h1 :: h2 :: t2) h_len
      cases' valid_pairs with head tail
      · contradiction
      · use (valid_pairs.foldl (fun acc (a, b) => 
          if |b - a| < |acc.2 - acc.1| then (a, b) else acc) head)
        constructor
        · simp [valid_pairs]
        · intro h_len_ge
          have h_head_valid : head.1 ≤ head.2 := valid_pairs_all_valid (h1 :: h2 :: t2) head (List.mem_cons_self _ _)
          have h_head_in : head.1 ∈ (h1 :: h2 :: t2) ∧ head.2 ∈ (h1 :: h2 :: t2) := 
            valid_pairs_all_in_numbers (h1 :: h2 :: t2) head (List.mem_cons_self _ _)
          constructor
          · -- smaller ≤ larger
            apply foldl_preserves_property
            · exact h_head_valid
            · intro acc pair
              simp
              split_ifs
              · simp
              · simp
          constructor
          · -- smaller ∈ numbers
            apply foldl_preserves_property
            · exact h_head_in.1
            · intro acc pair h_acc_in
              simp
              split_ifs
              · simp [List.mem_cons_iff]
                left
                exact h_head_in.1
              · exact h_acc_in
          constructor
          · -- larger ∈ numbers
            apply foldl_preserves_property
            · exact h_head_in.2
            · intro acc pair h_acc_in
              simp
              split_ifs
              · simp [List.mem_cons_iff]
                left
                exact h_head_in.2
              · exact h_acc_in
          constructor
          · -- minimality property
            intro x y hx hy
            simp
            exact abs_nonneg _
          · -- duplicate handling
            intro h_eq
            simp
            exact Nat.one_le_iff_ne_zero.mpr (List.length_pos_iff_ne_nil.mpr (List.ne_nil_of_mem (h_head_in.1)))