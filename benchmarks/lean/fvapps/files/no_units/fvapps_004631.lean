-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nthterm (first n c : Int) : Int := sorry

theorem nthterm_first_term 
  (first c : Int) : nthterm first 0 c = first := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nthterm_consecutive_diff 
  (first n c : Int) (h : n ≥ 0) : 
  nthterm first (n + 1) c - nthterm first n c = c := sorry

theorem nthterm_linear 
  (first n c : Int) (h : n ≥ 0) :
  nthterm first n c = first + n * c := sorry

theorem nthterm_additive 
  (first n1 n2 c : Int) (h1 : n1 ≥ 0) (h2 : n2 ≥ 0) :
  nthterm first (n1 + n2) c = nthterm (nthterm first n1 c) n2 c := sorry
-- </vc-theorems>