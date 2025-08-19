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
def find_closest_pair (numbers: List Rat): (Rat × Rat) :=
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

def implementation (numbers: List Rat): (Rat × Rat) := find_closest_pair numbers

-- LLM HELPER
lemma list_product_mem {α : Type*} (l : List α) (x y : α) : 
  x ∈ l → y ∈ l → (x, y) ∈ List.product l l := by
  intro hx hy
  exact List.mem_product.mpr ⟨hx, hy⟩

-- LLM HELPER
lemma filter_nonempty_of_mem {α : Type*} (l : List α) (p : α → Bool) :
  (∃ x, x ∈ l ∧ p x) → l.filter p ≠ [] := by
  intro h
  cases' h with x hx
  cases' hx with h1 h2
  rw [List.filter_eq_nil_iff]
  push_neg
  exact ⟨x, h1, h2⟩

-- LLM HELPER
lemma exists_le_pair_in_list (numbers : List Rat) (h : 2 ≤ numbers.length) :
  ∃ x y, x ∈ numbers ∧ y ∈ numbers ∧ x ≤ y := by
  cases' numbers with a as
  · simp at h
  cases' as with b bs
  · simp at h
  use a, b
  constructor
  · exact List.mem_cons_self a (b :: bs)
  constructor
  · exact List.mem_cons_of_mem a (List.mem_cons_self b bs)
  · exact le_total a b |>.elim id (fun h => h)

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h_len
    unfold implementation find_closest_pair
    cases' numbers with a as
    · simp at h_len
    cases' as with b bs
    · simp at h_len
    simp only [List.length_cons] at h_len
    -- We have at least 2 elements, so we can proceed
    have h_nonempty : (List.product (a :: b :: bs) (a :: b :: bs)).filter (fun (x, y) => x ≤ y) ≠ [] := by
      apply filter_nonempty_of_mem
      use (a, b)
      constructor
      · exact list_product_mem (a :: b :: bs) a b (List.mem_cons_self a (b :: bs)) (List.mem_cons_of_mem a (List.mem_cons_self b bs))
      · exact le_total a b |>.elim (fun h => by simp [h]) (fun h => by simp [h])
    cases' h_eq : (List.product (a :: b :: bs) (a :: b :: bs)).filter (fun (x, y) => x ≤ y) with
    | nil => contradiction
    | cons p ps =>
      -- The result is ps.foldl (fun acc (a, b) => if |b - a| < |acc.2 - acc.1| then (a, b) else acc) p
      have h_p_mem : p ∈ (List.product (a :: b :: bs) (a :: b :: bs)).filter (fun (x, y) => x ≤ y) := by
        rw [h_eq]
        exact List.mem_cons_self p ps
      have h_p_valid : p.1 ≤ p.2 := by
        rw [←List.mem_filter] at h_p_mem
        exact h_p_mem.2
      have h_p_in_list : p.1 ∈ (a :: b :: bs) ∧ p.2 ∈ (a :: b :: bs) := by
        rw [←List.mem_filter] at h_p_mem
        rw [List.mem_product] at h_p_mem
        exact h_p_mem.1
      -- The foldl operation preserves the properties we need
      sorry