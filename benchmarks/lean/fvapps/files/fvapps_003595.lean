-- <vc-preamble>
def pen (n : Int) : Int := (3*n*n - n) / 2

def gen_pen (n : Int) : Int :=
  if n >= 0 then (3*n*n - n) / 2 else (3*n*n + n) / 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def p_num (n : Int) : Bool :=
sorry

def g_p_num (n : Int) : Bool :=
sorry

def s_p_num (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem g_p_num_for_gen_pen (n : Int) : g_p_num (gen_pen n) = true :=
sorry

theorem s_p_num_is_square_of_pentagonal_number {n : Int} (h : s_p_num n = true) :
  ∃ k : Int,
    k * k = n ∧
    p_num k = true ∧
    g_p_num n = true :=
sorry

theorem non_square_not_s_p_num {n : Int} (h : ¬∃ k : Int, k * k = n) :
  s_p_num n = false :=
sorry
-- </vc-theorems>