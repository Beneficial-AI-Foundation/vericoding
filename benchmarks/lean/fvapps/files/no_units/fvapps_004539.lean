-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def π : Float := 3.14159265359
def series (k : Int) (nb : Nat) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem even_k_independent_of_nb (k : Int) (h1 : k ≠ 0) (h2 : k % 2 = 0) :
  ∀ nb : Nat, (series k nb - series k 0).abs < 1e-10 := sorry

theorem even_k_is_finite (k : Int) (h1 : k ≠ 0) (h2 : k % 2 = 0) :
  ∃ x : Float, series k 0 = x := sorry

theorem odd_k_is_finite (k : Int) (h1 : k > 0) (h2 : k % 2 = 1) (nb : Nat) :
  ∃ x : Float, series k nb = x := sorry

theorem series_2_is_pi_squared_div_6 : 
  (series 2 0 - π^2/6).abs < 1e-10 := sorry
-- </vc-theorems>