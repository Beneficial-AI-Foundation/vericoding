-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_testcase : (Nat × List (Nat × Nat)) := sorry

theorem testcase_properties (n : Nat) (balloons : List (Nat × Nat)) 
    (h : (n, balloons) = generate_testcase) : 
    List.length balloons = n ∧ 
    (List.get? balloons 0).map Prod.fst = some 0 ∧
    List.all balloons (fun p => p.1 ≥ 0 ∧ p.2 > 0) ∧
    List.Pairwise (fun p1 p2 => p1.1 < p2.1) balloons := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>