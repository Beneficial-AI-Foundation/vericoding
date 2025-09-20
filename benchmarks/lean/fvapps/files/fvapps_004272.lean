-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def geometric_sequence_elements (a r n : Int) : String := sorry

theorem geometric_sequence_correct {a r n : Int} (h : n > 0) (hr : r ≠ 0) :
  let terms := (geometric_sequence_elements a r n).splitOn ", ";
  -- sequence has correct length
  terms.length = n
  -- first term is a
  ∧ terms.head? = some (toString a)
  -- each term follows geometric sequence rule
  ∧ ∀ i : Nat, 0 < i → i < n → 
      match terms.get? i, terms.get? (i-1) with
      | some curr, some prev => curr.toInt! = prev.toInt! * r
      | _, _ => False := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_term_sequence {a r : Int} (hr : r ≠ 0) :
  geometric_sequence_elements a r 1 = toString a := sorry
-- </vc-theorems>