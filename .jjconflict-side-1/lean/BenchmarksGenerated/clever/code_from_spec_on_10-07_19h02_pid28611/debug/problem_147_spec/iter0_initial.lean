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
    rw [Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod, Nat.zero_mod]
    norm_num
  · cases' k with k'
    · simp [h]
      rw [Nat.mul_mod, h, Nat.one_mul, Nat.one_mod]
      norm_num
    · cases' k' with k''
      · simp [h]
        rw [Nat.mul_mod, h, Nat.mul_mod]
        norm_num
      · have : k'' + 3 = k' + 2 := by simp [Nat.add_assoc]
        have : k' + 2 ≥ 3 := by 
          cases' k'' with k'''
          · norm_num
          · simp [Nat.add_assoc]; norm_num
        have : i % 3 ≥ 3 := by rw [h]; exact this
        have : i % 3 < 3 := Nat.mod_lt i (by norm_num)
        linarith

-- LLM HELPER
lemma sum_three_a_seq_mod_3 (i j k : Nat) : 
  (a_seq i + a_seq j + a_seq k) % 3 = 0 ↔ 
  (i % 3 = 0 ∧ j % 3 = 0 ∧ k % 3 = 0) ∨ 
  (i % 3 ≠ 0 ∧ j % 3 ≠ 0 ∧ k % 3 ≠ 0) := by
  rw [Nat.add_mod, Nat.add_mod]
  repeat rw [a_seq_mod_3]
  split_ifs with h1 h2 h3
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]

-- LLM HELPER
def valid_triple (n : Nat) (triple : Nat × Nat × Nat) : Prop :=
  let (i, j, k) := triple
  1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
  (a_seq i + a_seq j + a_seq k) % 3 = 0

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
  ∀ (triple: Nat × Nat × Nat),
    let (i, j, k) := triple;
    let a_i := i * i - i + 1;
    let a_j := j * j - j + 1;
    let a_k := k * k - k + 1;
    (1 ≤ i ∧ i < j ∧ j < k ∧ k ≤ n ∧
    (a_i + a_j + a_k) % 3 = 0)
    ↔ triple ∈ S_witness n := by
  intro triple
  simp [S_witness, valid_triple, a_seq]
  cases' triple with i jk
  cases' jk with j k
  simp
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
lemma count_triples_eq_card (n : Nat) : count_triples n = (S_witness n).card := by
  simp [count_triples, S_witness]
  rw [Finset.card_eq_sum_ones]
  congr

def implementation (n: Nat) : Nat := count_triples n

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use S_witness n
  constructor
  · exact count_triples_eq_card n
  · exact S_witness_correct n