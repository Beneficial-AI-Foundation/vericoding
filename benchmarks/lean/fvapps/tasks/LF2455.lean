-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def wrap_text (text : String) (width : Nat) : String := sorry

-- Invalid width theorem
-- </vc-definitions>

-- <vc-theorems>
theorem wrap_text_invalid_width (text : String) (width : Int) :
  width ≤ 0 → wrap_text text width.toNat = "" := sorry 

-- Width one theorem

theorem wrap_text_width_one (text : String) :
  text ≠ "" →
  let lines := (wrap_text text 1).split (· = '\n')
  ∀ i : Fin lines.length, 
    i.val < lines.length - 1 → 
    (lines[i]).length = 1 := sorry

-- Basic width constraint theorem  

theorem wrap_text_basic (text : String) (width : Nat) :
  width > 0 →
  let lines := (wrap_text text width).split (· = '\n')
  ∀ line ∈ lines, line.length ≤ width := sorry
-- </vc-theorems>