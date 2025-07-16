import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
∃ (S : Finset (Nat × Nat × Nat)), S.card = result ∧
  ∀ (triple: Nat × Nat × Nat),
    let (i, j, k) := triple;
    let a_i := i * i - i + 1;
    let a_j := j * j - j + 1;
    let a_k := k * k - k + 1;
    (1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
    (a_i + a_j + a_k) % 3 = 0)
    ↔ triple ∈ S
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def a_seq (i : Nat) : Nat := i * i - i + 1

-- LLM HELPER
lemma a_seq_mod_3 (i : Nat) : a_seq i % 3 = if i % 3 = 0 then 1 else 0 := by
  simp [a_seq]
  cases' h : i % 3 with k
  · simp [h]
    have : i = 3 * (i / 3) := by
      rw [Nat.mul_div_cancel']
      exact Nat.dvd_iff_mod_eq_zero.mpr h
    rw [this]
    ring_nf
    norm_num
  · cases' k with k'
    · simp [h]
      have : i = 3 * (i / 3) + 1 := by
        rw [Nat.div_add_mod i 3]
        simp [h]
      rw [this]
      ring_nf
      norm_num
    · cases' k' with k''
      · simp [h]
        have : i = 3 * (i / 3) + 2 := by
          rw [Nat.div_add_mod i 3]
          simp [h]
        rw [this]
        ring_nf
        norm_num
      · have : i % 3 = k'' + 3 := by simp [h]
        have : i % 3 < 3 := Nat.mod_lt i (by norm_num)
        linarith

-- LLM HELPER
def valid_triple (n : Nat) (triple : Nat × Nat × Nat) : Prop :=
  let (i, j, k) := triple
  1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
  (a_seq i + a_seq j + a_seq k) % 3 = 0

-- LLM HELPER
instance valid_triple_decidable (n : Nat) : DecidablePred (valid_triple n) := by
  intro triple
  simp [valid_triple]
  infer_instance

-- LLM HELPER
def count_triples (n : Nat) : Nat :=
  (Finset.range (n + 1)).sum (fun i =>
    if i = 0 then 0 else
      (Finset.range (n + 1)).sum (fun j =>
        if j ≤ i then 0 else
          (Finset.range (n + 1)).sum (fun k =>
            if k ≤ j then 0 else
              if (a_seq i + a_seq j + a_seq k) % 3 = 0 then 1 else 0)))

-- LLM HELPER
def S_witness (n : Nat) : Finset (Nat × Nat × Nat) :=
  Finset.filter (valid_triple n) 
    (Finset.product (Finset.range (n + 1)) 
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))))

-- LLM HELPER
lemma S_witness_correct (n : Nat) : 
  ∀ (i j k : Nat),
    (1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
    (i * i - i + 1 + (j * j - j + 1) + (k * k - k + 1)) % 3 = 0)
    ↔ (i, j, k) ∈ S_witness n := by
  intro i j k
  simp [S_witness, valid_triple, a_seq]
  constructor
  · intro h
    constructor
    · exact h.2.2.2
    · constructor
      · exact Nat.lt_succ_of_le (Nat.le_of_lt h.2.1)
      · constructor
        · exact Nat.lt_succ_of_le (Nat.le_of_lt h.2.2.1)
        · constructor
          · exact Nat.lt_succ_of_le h.2.2.2
          · exact h
  · intro h
    exact h.2.2.2.2

-- LLM HELPER
lemma count_triples_eq_card (n : Nat) : (S_witness n).card = count_triples n := by
  simp [count_triples, S_witness]
  rw [Finset.card_eq_sum_ones]
  simp [valid_triple, a_seq]
  rw [Finset.sum_product, Finset.sum_product]
  congr 1
  ext i
  congr 1
  ext p
  simp [Finset.sum_range_succ]
  cases' p with j k
  congr 1
  ext j
  congr 1
  ext k
  simp
  split_ifs with h1 h2 h3 h4
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all

def implementation (n: Nat) : Nat := 
  (Finset.filter (valid_triple n) 
    (Finset.product (Finset.range (n + 1)) 
      (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))))).card

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use S_witness n
  constructor
  · rfl
  · intro triple
    cases' triple with i p
    cases' p with j k
    simp [a_seq, S_witness, valid_triple]
    constructor
    · intro h
      constructor
      · exact h.2.2.2
      · constructor
        · exact Nat.lt_succ_of_le (Nat.le_of_lt h.2.1)
        · constructor
          · exact Nat.lt_succ_of_le (Nat.le_of_lt h.2.2.1)
          · constructor
            · exact Nat.lt_succ_of_le h.2.2.2
            · exact h
    · intro h
      exact h.2.2.2.2