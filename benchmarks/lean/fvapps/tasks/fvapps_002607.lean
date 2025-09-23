-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def wheat_from_chaff (xs : List Int) : List Int := sorry

theorem wheat_from_chaff_length 
    (xs : List Int) :
    (wheat_from_chaff xs).length = xs.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wheat_from_chaff_perm 
    (xs : List Int) : 
    List.Perm (wheat_from_chaff xs) xs := sorry

theorem wheat_from_chaff_partition
    (xs : List Int)
    (i j : Nat)
    (hi : i < (wheat_from_chaff xs).length)
    (hj : j < (wheat_from_chaff xs).length)
    (h : i < j) :
    ((wheat_from_chaff xs).get ⟨i,hi⟩ ≥ 0) →
    ((wheat_from_chaff xs).get ⟨j,hj⟩ ≥ 0) := sorry

theorem wheat_from_chaff_all_pos
    (xs : List Int)
    (h : ∀ x ∈ xs, x > 0) :
    wheat_from_chaff xs = xs := sorry

theorem wheat_from_chaff_all_neg
    (xs : List Int)
    (h : ∀ x ∈ xs, x < 0) :
    wheat_from_chaff xs = xs := sorry

theorem wheat_from_chaff_empty :
    wheat_from_chaff [] = [] := sorry
-- </vc-theorems>