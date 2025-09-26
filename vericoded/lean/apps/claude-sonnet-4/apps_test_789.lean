import Mathlib
-- <vc-preamble>
def ValidLuckyNumber (n : String) : Prop :=
  n.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < n.length → n.get (String.Pos.mk i) = '4' ∨ n.get (String.Pos.mk i) = '7'

partial def convertToBinary (n : String) : String :=
  if n.length = 0 then ""
  else if n.get ⟨0⟩ = '4' then 
    "0" ++ convertToBinary (n.drop 1)
  else 
    "1" ++ convertToBinary (n.drop 1)

def pow2 : Nat → Nat
| 0 => 1
| n + 1 => 2 * pow2 n

partial def binaryToInt (s : String) : Nat :=
  if s.length = 0 then 0
  else if s.get ⟨0⟩ = '1' then 
    pow2 (s.length - 1) + binaryToInt (s.drop 1)
  else 
    binaryToInt (s.drop 1)

def ValidResult (n : String) (result : Int) : Prop :=
  ValidLuckyNumber n →
  (result > 0 ∧ result = 2 * (↑(pow2 (n.length - 1)) - 1) + ↑(binaryToInt (convertToBinary n)) + 1)

@[reducible, simp]
def solve_precond (n : String) : Prop :=
  ValidLuckyNumber n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma about pow2 being positive
lemma pow2_pos (n : Nat) : pow2 n > 0 := by
  induction n with
  | zero => simp [pow2]
  | succ n ih => simp [pow2]; omega

-- LLM HELPER: Lemma about binaryToInt being non-negative
lemma binaryToInt_nonneg (s : String) : (binaryToInt s : Int) ≥ 0 := by
  exact Nat.cast_nonneg (binaryToInt s)
-- </vc-helpers>

-- <vc-definitions>
def solve (n : String) (h_precond : solve_precond n) : Int :=
  2 * (↑(pow2 (n.length - 1)) - 1) + ↑(binaryToInt (convertToBinary n)) + 1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : String) (result : Int) (h_precond : solve_precond n) : Prop :=
  ValidResult n result

theorem solve_spec_satisfied (n : String) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond ValidResult
  intro h_valid
  constructor
  · -- Prove result > 0
    simp [solve]
    -- We have 2 * (2^(n.length-1) - 1) + binaryToInt(...) + 1
    -- Since n.length > 0 from ValidLuckyNumber, we have n.length - 1 ≥ 0
    -- So pow2 (n.length - 1) ≥ 1, making the whole expression positive
    have h_len : n.length > 0 := h_valid.1
    have h_pow2_pos : pow2 (n.length - 1) > 0 := pow2_pos (n.length - 1)
    have h_binaryToInt_nonneg : (binaryToInt (convertToBinary n) : Int) ≥ 0 := binaryToInt_nonneg (convertToBinary n)
    omega
  · -- Prove equality
    simp [solve]
-- </vc-theorems>
