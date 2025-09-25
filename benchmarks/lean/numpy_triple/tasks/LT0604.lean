-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def center {n : Nat} (a : Vector String n) (width : Vector Nat n) (fillchar : Char := ' ') : Id (Vector String n) :=
  return Vector.ofFn (fun i => 
    let str := a.get i
    let w := width.get i
    if str.length ≥ w then 
      str 
    else 
      let padding := w - str.length
      let left_pad := padding / 2
      let right_pad := padding - left_pad
      String.mk (List.replicate left_pad fillchar) ++ str ++ String.mk (List.replicate right_pad fillchar))
-- </vc-definitions>

-- <vc-theorems>
theorem center_spec {n : Nat} (a : Vector String n) (width : Vector Nat n) (fillchar : Char := ' ') :
    ⦃⌜True⌝⦄
    center a width fillchar
    ⦃⇓r => ⌜∀ i : Fin n, 
      -- Length preservation: If original string length >= target width, return original
      ((a.get i).length ≥ width.get i → r.get i = a.get i) ∧
      -- Width compliance: Result length equals max(original.length, target_width)
      (r.get i).length = max (a.get i).length (width.get i) ∧
      -- Symmetric padding: If original string length < target width, pad symmetrically
      ((a.get i).length < width.get i → 
        ∃ (left_pad right_pad : Nat), 
          left_pad + (a.get i).length + right_pad = width.get i ∧
          -- Padding should be as equal as possible (differ by at most 1)
          (left_pad = right_pad ∨ left_pad = right_pad + 1) ∧
          -- Left padding is floor(padding/2), right padding is ceiling(padding/2)
          left_pad = (width.get i - (a.get i).length) / 2 ∧
          right_pad = (width.get i - (a.get i).length) - left_pad ∧
          -- Result string structure: left_pad + original + right_pad
          r.get i = (String.mk (List.replicate left_pad fillchar)) ++ (a.get i) ++ (String.mk (List.replicate right_pad fillchar)))⌝⦄ := by
  sorry
-- </vc-theorems>