-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_blocks (w l h : Nat) : Nat := sorry

theorem num_blocks_positive (w l h : Nat) (hw : w > 0) (hl : l > 0) (hh : h > 0) : 
  num_blocks w l h > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_blocks_base_layer (w l h : Nat) (hw : w > 0) (hl : l > 0) (hh : h > 0) :
  num_blocks w l h ≥ w * l := sorry 

theorem num_blocks_all_layers (w l h : Nat) (hw : w > 0) (hl : l > 0) (hh : h > 0) :
  num_blocks w l h ≥ w * l * h := sorry

theorem num_blocks_symmetric (w l h : Nat) :
  num_blocks w l h = num_blocks l w h := sorry
-- </vc-theorems>