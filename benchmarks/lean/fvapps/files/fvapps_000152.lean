-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxArea (h w : Nat) (horizontalCuts verticalCuts : List Nat) : Nat := sorry

theorem maxArea_single_cut
  (h w : Nat)
  (h_ge : h ≥ 2)
  (w_ge : w ≥ 2) :
  maxArea h w [h/2] [w/2] = max (h/2) (h - h/2) * max (w/2) (w - w/2) := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>