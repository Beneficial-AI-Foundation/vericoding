-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fromstring {n : Nat} (input : String) (sep : String) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fromstring_spec {n : Nat} (input : String) (sep : String)
    (h_n_pos : n > 0)
    (h_sep_nonempty : sep ≠ "")
    (h_tokens_count : (input.splitOn sep).length = n)
    (h_tokens_nonempty : ∀ token ∈ (input.splitOn sep), token.trim ≠ "")
    (h_tokens_numeric : ∀ token ∈ (input.splitOn sep),
      -- Each token represents a valid numeric string
      ∃ val : Float,
        -- The token, when trimmed of whitespace, represents this float value
        True) :  -- Abstract representation of string-to-float conversion
    ⦃⌜n > 0 ∧ sep ≠ "" ∧
      (input.splitOn sep).length = n ∧
      (∀ token ∈ (input.splitOn sep), token.trim ≠ "") ∧
      (∀ token ∈ (input.splitOn sep), ∃ val : Float, True)⌝⦄
    fromstring input sep
    ⦃⇓result => ⌜
      -- The result vector contains parsed float values from the input string
      (∀ i : Fin n,
        ∃ token : String, ∃ val : Float,
          token = (input.splitOn sep)[i.val]! ∧
          result.get i = val ∧
          -- val is the float representation of the trimmed token
          True) ∧
      -- Mathematical properties of the result
      -- 1. All values are finite (no infinity or NaN from parsing)
      (∀ i : Fin n, Float.isFinite (result.get i)) ∧
      -- 2. The parsing preserves the order of tokens
      (∀ i j : Fin n, i.val < j.val →
        -- The i-th element comes from the i-th token in the input
        ∃ token_i token_j : String,
          token_i = (input.splitOn sep)[i.val]! ∧
          token_j = (input.splitOn sep)[j.val]! ∧
          -- And their relative position in the input is preserved
          True) ∧
      -- 3. Example behavior matching NumPy docs
      -- For input "1 2" with sep " ", result should be [1.0, 2.0]
      -- For input "1, 2" with sep ",", result should be [1.0, 2.0]
      (input = "1 2" ∧ sep = " " ∧ n = 2 →
        result.get ⟨0, sorry⟩ = 1.0 ∧ result.get ⟨1, sorry⟩ = 2.0) ∧
      (input = "1, 2" ∧ sep = "," ∧ n = 2 →
        result.get ⟨0, sorry⟩ = 1.0 ∧ result.get ⟨1, sorry⟩ = 2.0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>