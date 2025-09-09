-- <vc-helpers>
-- </vc-helpers>

def coffee_limits (y : Int) (m : Int) (d : Int) : List Int := sorry
def limit (h : Int) (c : Int) : Int := sorry

theorem coffee_limits_valid_output {y m d : Int} (h1 : y ≥ 1950) (h2 : y ≤ 2024) 
    (h3 : m ≥ 1) (h4 : m ≤ 12) (h5 : d ≥ 1) (h6 : d ≤ 28) :
    let result := coffee_limits y m d
    List.length result = 2 ∧ 
    ∀ x ∈ result, x ≥ 0 ∧ x < 5000 := sorry

theorem limit_output_bounds {h c : Int} (h1 : h ≥ 0) (h2 : c ≥ 0) :
    let result := limit h c
    result ≥ 0 ∧ result < 5000 := sorry

theorem limit_deterministic {h c : Int} :
    limit h c = limit h c := sorry

/-
info: [2645, 1162]
-/
-- #guard_msgs in
-- #eval coffee_limits 1950 1 19

/-
info: [111, 0]
-/
-- #guard_msgs in
-- #eval coffee_limits 1965 12 11

/-
info: [0, 11]
-/
-- #guard_msgs in
-- #eval coffee_limits 1964 11 28

-- Apps difficulty: introductory
-- Assurance level: unguarded