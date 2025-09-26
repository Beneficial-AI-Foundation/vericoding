-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_bad_luck (strings : List String) : Nat :=
sorry

def countChar (c : Char) (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_bad_luck_non_negative (strings : List String) :
  find_min_bad_luck strings ≥ 0 :=
sorry

theorem find_min_bad_luck_leq_min_len (strings : List String) :
  strings ≠ [] → find_min_bad_luck strings ≤ List.foldr (fun s acc => min s.length acc) (strings[0]!.length) strings.tail :=
sorry
-- </vc-theorems>