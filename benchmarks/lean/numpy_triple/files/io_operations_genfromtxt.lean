-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def genfromtxt {rows cols : Nat} (input : Vector String rows) 
    (delimiter : String) (fill_value : Float) (skip_header : Nat) :
    Id (Vector (Vector Float cols) (rows - skip_header)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem genfromtxt_spec {rows cols : Nat} (input : Vector String rows) 
    (delimiter : String) (fill_value : Float) (skip_header : Nat)
    (h_skip : skip_header < rows)
    (h_well_formed : ∀ i : Fin (rows - skip_header), 
      let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
      (input.get line_idx).splitOn delimiter |>.length = cols) :
    ⦃⌜skip_header < rows ∧ 
      ∀ i : Fin (rows - skip_header), 
        let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
        (input.get line_idx).splitOn delimiter |>.length = cols⌝⦄
    genfromtxt input delimiter fill_value skip_header
    ⦃⇓result => ⌜
      (result.size = rows - skip_header) ∧
      (∀ i : Fin (rows - skip_header), 
        (result.get i).size = cols) ∧
      (∀ i : Fin (rows - skip_header), ∀ j : Fin cols,
          let line_idx : Fin rows := ⟨i.val + skip_header, by omega⟩
          let line := input.get line_idx
          let fields := line.splitOn delimiter
          let field_str := if h : j.val < fields.length then fields.get ⟨j.val, h⟩ else ""
          (result.get i).get j = if field_str.isEmpty ∨ field_str.trim.isEmpty then 
                                   fill_value 
                                 else 
                                   field_str.toNat!.toFloat)⌝⦄ := by
  sorry
-- </vc-theorems>