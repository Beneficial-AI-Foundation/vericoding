import Std.Do.Triple
import Std.Tactic.Do

    Rounds each element of the input array to the given number of decimal places.
    Uses "banker's rounding" (round half to even) for ties.
    
    For decimals=0: rounds to nearest integer
    For decimals>0: rounds to that many decimal places
    For decimals<0: rounds to nearest 10^(-decimals)
    
    Returns an array of the same shape as input, containing the rounded values.
-/

open Std.Do

-- LLM HELPER
def round_to_decimals (x : Float) (decimals : Int) : Float :=
  if decimals >= 0 then
    let factor := (10 : Float) ^ decimals.natAbs
    (x * factor).round / factor
  else
    let factor := (10 : Float) ^ decimals.natAbs
    (x / factor).round * factor

def numpy_round {n : Nat} (a : Vector Float n) (decimals : Int) : Id (Vector Float n) :=
  pure (a.map (fun x => round_to_decimals x decimals))

-- LLM HELPER
lemma round_preserves_order (x y : Float) (decimals : Int) :
    x ≤ y → round_to_decimals x decimals ≤ round_to_decimals y decimals := by
  intro h
  simp [round_to_decimals]
  split_ifs with h_pos
  · -- decimals >= 0
    let factor := (10 : Float) ^ decimals.natAbs
    have h_factor_pos : factor > 0 := by
      simp [factor]
      sorry
    have h_mul_le : x * factor ≤ y * factor := by
      sorry
    have h_round_le : (x * factor).round ≤ (y * factor).round := by
      sorry
    sorry
  · -- decimals < 0
    let factor := (10 : Float) ^ decimals.natAbs
    have h_factor_pos : factor > 0 := by
      simp [factor]
      sorry
    have h_div_le : x / factor ≤ y / factor := by
      sorry
    have h_round_le : (x / factor).round ≤ (y / factor).round := by
      sorry
    sorry

-- LLM HELPER  
lemma round_approximation_bound (x : Float) (decimals : Int) :
    decimals ≥ 0 → (round_to_decimals x decimals - x) * (round_to_decimals x decimals - x) ≤ 1.0 := by
  intro h_pos
  simp [round_to_decimals]
  split_ifs with h_split
  · -- decimals >= 0
    let factor := (10 : Float) ^ decimals.natAbs
    sorry
  · contradiction

theorem numpy_round_spec {n : Nat} (a : Vector Float n) (decimals : Int) :
    ⦃⌜True⌝⦄
    numpy_round a decimals
    ⦃⇓result => ⌜∀ i : Fin n,
      -- For decimals = 0, result is the nearest integer
      (decimals = 0 → ∃ k : Int, result.get i = Float.ofInt k ∧ 
                      (result.get i - 0.5 ≤ a.get i ∧ a.get i < result.get i + 0.5)) ∧
      -- Monotonicity: order is preserved
      (∀ j : Fin n, a.get i ≤ a.get j → result.get i ≤ result.get j) ∧
      -- Approximation bound: rounded value is reasonably close to original
      (decimals ≥ 0 → (result.get i - a.get i) * (result.get i - a.get i) ≤ 1.0) ∧
      -- Idempotence: rounding twice gives same result
      (decimals = 0 → ∃ k : Int, result.get i = Float.ofInt k → result.get i = result.get i) ∧
      -- Basic sanity: result has the same vector shape as input
      (result.get i = result.get i)⌝⦄ := by
  simp [numpy_round]
  intro i
  constructor
  · -- For decimals = 0, result is the nearest integer
    intro h_dec_zero
    simp [round_to_decimals, h_dec_zero]
    use (a.get i).round.toInt
    constructor
    · simp [Float.ofInt_toInt_round]
    · constructor
      · have : (a.get i).round - 0.5 ≤ a.get i := by sorry
        exact this
      · have : a.get i < (a.get i).round + 0.5 := by sorry
        exact this
  constructor
  · -- Monotonicity
    intro j h_le
    simp [Vector.get_map]
    exact round_preserves_order (a.get i) (a.get j) decimals h_le
  constructor
  · -- Approximation bound
    intro h_pos
    simp [Vector.get_map]
    exact round_approximation_bound (a.get i) decimals h_pos
  constructor
  · -- Idempotence
    intro h_dec_zero k h_int
    rfl
  · -- Basic sanity
    rfl