-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dad_filter (s : String) : String := sorry

def containsDoubleComma (s : String) : Bool := 
  let rec check (chars : List Char) : Bool := 
    match chars with
    | [] => false
    | [_] => false
    | x :: y :: rest => 
      if x == ',' && y == ',' then true
      else check (y :: rest)
  check s.data
  termination_by check chars => chars.length
-- </vc-definitions>

-- <vc-theorems>
theorem dad_filter_no_double_commas {s : String} {n : Nat} (h : n > 0 ∧ n ≤ 10) :
  containsDoubleComma (dad_filter (s ++ String.mk (List.replicate n ','))) = false := sorry

theorem dad_filter_no_trailing_comma {s : String} :
  ¬ String.endsWith (dad_filter s) "," := sorry

theorem dad_filter_no_trailing_space {s : String} :
  ¬ String.endsWith (dad_filter s) " " := sorry

theorem dad_filter_preserves_noncomma_chars {s : String} :
  (String.replace s "," "").trim = (String.replace (dad_filter s) "," "").trim := sorry

theorem dad_filter_idempotent {s : String} :
  dad_filter (dad_filter s) = dad_filter s := sorry
-- </vc-theorems>