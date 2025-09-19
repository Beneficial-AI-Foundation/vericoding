-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_it (seq: List Int) : Int := sorry

theorem find_it_exists_in_odds {seq: List Int} (h: seq ≠ []) :
  let result := find_it seq
  let odds := seq.filter (fun x => seq.count x % 2 = 1)
  odds ≠ [] → odds.contains result := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>