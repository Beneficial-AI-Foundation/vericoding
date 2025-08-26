import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.polynomial.polyutils.trimseq",
  "category": "Polynomial utilities",
  "description": "Remove small Poly series coefficients.",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.polynomial.polyutils.trimseq.html",
  "doc": "Remove small Poly series coefficients.\n\n    Parameters\n    ----------\n    seq : sequence\n        Sequence of Poly series coefficients.\n\n    Returns\n    -------\n    series : sequence\n        Subsequence with trailing zeros removed. If the resulting sequence\n        would be empty, return the first element. The returned sequence may\n        or may not be a view.\n\n    Notes\n    -----\n    Do not lose the type info if the sequence contains unknown objects.",
  "code": "def trimseq(seq):\n    \"\"\"Remove small Poly series coefficients.\n\n    Parameters\n    ----------\n    seq : sequence\n        Sequence of Poly series coefficients.\n\n    Returns\n    -------\n    series : sequence\n        Subsequence with trailing zeros removed. If the resulting sequence\n        would be empty, return the first element. The returned sequence may\n        or may not be a view.\n\n    Notes\n    -----\n    Do not lose the type info if the sequence contains unknown objects.\n\n    \"\"\"\n    if len(seq) == 0 or seq[-1] != 0:\n        return seq\n    else:\n        for i in range(len(seq) - 1, -1, -1):\n            if seq[i] != 0:\n                break\n        return seq[:i + 1]"
}
-/

open Std.Do

/-- Remove trailing zeros from a sequence of polynomial coefficients.
    Returns the sequence with trailing zeros removed. If the sequence would be empty 
    after trimming, returns the first element. Empty sequences are handled. -/
def trimseq {n : Nat} (seq : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: trimseq removes trailing zeros while preserving at least one element.
    For non-empty sequences, if the last element is non-zero, return the sequence unchanged.
    If the last element is zero, trim trailing zeros but always keep at least one element. -/
theorem trimseq_spec {n : Nat} (seq : Vector Float n) :
    ⦃⌜True⌝⦄
    trimseq seq
    ⦃⇓result => ⌜-- Result has same length as input
                 result.toList.length = n ∧
                 -- If empty or last element is non-zero, return unchanged
                 (n = 0 ∨ (n > 0 ∧ seq.get ⟨n - 1, sorry⟩ ≠ 0) → result = seq) ∧
                 -- If last element is zero, trim properly
                 (n > 0 ∧ seq.get ⟨n - 1, sorry⟩ = 0 → 
                   -- There exists a position k where trimming occurs
                   (∃ k : Fin n, 
                    -- All elements after k in original sequence are zero
                    (∀ j : Fin n, j.val > k.val → seq.get j = 0) ∧
                    -- Result preserves elements up to k, zeros after
                    (∀ i : Fin n, i.val ≤ k.val → result.get i = seq.get i) ∧
                    (∀ i : Fin n, i.val > k.val → result.get i = 0) ∧
                    -- Element at k is non-zero unless k = 0 (all zeros case)
                    (k.val > 0 → seq.get k ≠ 0)))⌝⦄ := by
  sorry