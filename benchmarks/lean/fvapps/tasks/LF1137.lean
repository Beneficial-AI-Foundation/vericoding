-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_tour (s: String) : String := sorry

theorem short_strings_return_no 
    (s: String) 
    (h: s.length < 4) :
    solve_string_tour s = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strings_ending_1000_return_yes
    (s: String)
    (h1: s.length ≥ 4)
    (h2: s.endsWith "1000") :
    solve_string_tour s = "YES" := sorry

theorem strings_not_ending_1000_return_no
    (s: String)
    (h1: s.length ≥ 4)
    (h2: ¬ s.endsWith "1000") :
    solve_string_tour s = "NO" := sorry
-- </vc-theorems>