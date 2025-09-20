-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count (a: List Int) (t: Int) (x: Int) : Int := sorry

theorem count_bounded (a: List Int) (t: Int) (x: Int) (h: a.length > 0) :
  let result := count a t x
  0 ≤ result ∧ result ≤ a.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_zero_x (a: List Int) (t: Int) (h: a.length > 0) :
  count a t 0 = (a.filter (fun v => v = t)).length := sorry

theorem count_nonzero_x (a: List Int) (t: Int) (x: Int) (h1: a.length > 0) (h2: x ≠ 0) :
  count a t x = (a.filter (fun v => (t - v) % x = 0)).length := sorry
-- </vc-theorems>