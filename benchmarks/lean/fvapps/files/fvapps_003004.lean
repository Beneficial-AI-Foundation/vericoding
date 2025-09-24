-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multi (l : List Int) : Int :=
sorry

def add (l : List Int) : Int :=
sorry

def reverse (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multi_neutral (l : List Int) (h : l.length ≥ 1) :
  multi (l ++ [1]) = multi l :=
sorry

theorem multi_order_indep (l : List Int) (h : l.length ≥ 1) :
  multi l = multi l.reverse :=
sorry

theorem add_neutral (l : List Int) :
  add (l ++ [0]) = add l :=
sorry

theorem add_order_indep (l : List Int) :
  add l = add l.reverse :=
sorry

theorem add_recursive (l : List Int) (h : l ≠ []) :
  add l = add (l.take (l.length - 1)) + l.getLast h :=
sorry

theorem reverse_involution (s : String) :
  reverse (reverse s) = s :=
sorry

theorem reverse_preserves_length (s : String) :
  (reverse s).length = s.length :=
sorry

theorem reverse_first_last_char (s : String) (h₁ : s.length > 0) :
  let n := s.length
  let rs := reverse s
  rs.front = s.back ∧ rs.back = s.front :=
sorry
-- </vc-theorems>