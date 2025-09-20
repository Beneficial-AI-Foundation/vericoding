-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decode (n : Nat) : String := sorry

theorem decode_known_case1 :
  decode 103115104105123101118119981001098 = "codewars, 18" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decode_known_case2 :
  decode 119112105105116981000981091199810019810612111498100000110001 = "sleep, 8, is, 9, fun, 2097" := sorry

theorem decode_known_case3 :
  decode 120108105118105109119101112109107108120981001010101098102105108109114104125115121118105125105119981000 = "thereisalight, 1194, behindyoureyes, 8" := sorry
-- </vc-theorems>