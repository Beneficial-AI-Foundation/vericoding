-- <vc-preamble>
def listMax : List Int → Int
  | [] => 0
  | (x::xs) => max x (listMax xs)

def listSum : List Int → Int
  | [] => 0
  | (x::xs) => x + listSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_quadruples (n : Nat) (target : Int) (nums : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_quadruples_returns_natural
  (nums : List Int) (target : Int) (h : nums.length ≥ 4) :
  count_quadruples nums.length target nums ≥ 0 :=
sorry

theorem count_quadruples_binary_for_four
  (nums : List Int) (target : Int) (h : nums.length = 4) :
  count_quadruples nums.length target nums = 0 ∨
  count_quadruples nums.length target nums = 1 :=
sorry

theorem insufficient_elements_gives_zero
  (nums : List Int) (target : Int) (h : nums.length < 4) :
  count_quadruples nums.length target nums = 0 :=
sorry
-- </vc-theorems>