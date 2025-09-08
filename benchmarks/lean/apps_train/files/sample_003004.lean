/-
Debug the functions
Should be easy, begin by looking at the code. Debug the code and the functions should work.
There are three functions: ```Multiplication (x)``` ```Addition (+)``` and ```Reverse (!esreveR)```

i {
  font-size:16px;
}

#heading {
  padding: 2em;
  text-align: center;
  background-color: #0033FF;
  width: 100%;
  height: 5em;
}
-/

def multi (l : List Int) : Int := sorry
def add (l : List Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def reverse (s : String) : String := sorry

theorem multi_neutral (l : List Int) (h : l.length ≥ 1) :
  multi (l ++ [1]) = multi l := sorry

theorem multi_order_indep (l : List Int) (h : l.length ≥ 1) :
  multi l = multi l.reverse := sorry

theorem add_neutral (l : List Int) :
  add (l ++ [0]) = add l := sorry

theorem add_order_indep (l : List Int) :
  add l = add l.reverse := sorry

theorem add_recursive (l : List Int) (h : l ≠ []) :
  add l = add (l.take (l.length - 1)) + l.getLast h := sorry

theorem reverse_involution (s : String) :
  reverse (reverse s) = s := sorry

theorem reverse_preserves_length (s : String) :
  (reverse s).length = s.length := sorry

theorem reverse_first_last_char (s : String) (h₁ : s.length > 0) :
  let n := s.length
  let rs := reverse s
  rs.front = s.back ∧ rs.back = s.front := sorry

/-
info: 80
-/
-- #guard_msgs in
-- #eval multi [8, 2, 5]

/-
info: 6
-/
-- #guard_msgs in
-- #eval add [1, 2, 3]

/-
info: 'olleh'
-/
-- #guard_msgs in
-- #eval reverse "hello"

-- Apps difficulty: introductory
-- Assurance level: unguarded