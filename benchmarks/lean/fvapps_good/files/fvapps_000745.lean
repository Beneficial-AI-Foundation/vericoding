-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_similar_dishes (dish1 dish2 : List String) : String := sorry

theorem check_similar_dishes_valid_output
  (dish1 dish2 : List String)
  (h1 : dish1.length ≥ 4)
  (h2 : dish2.length ≥ 4) :
  (check_similar_dishes dish1 dish2 = "similar") ∨ 
  (check_similar_dishes dish1 dish2 = "dissimilar") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_similar_dishes_common_elements
  (dish1 dish2 : List String)
  (h1 : dish1.length ≥ 4)
  (h2 : dish2.length ≥ 4) :
  let common := (dish1.filter (fun x => dish2.contains x)).length
  check_similar_dishes dish1 dish2 = 
    if common ≥ 2 then "similar" else "dissimilar" := sorry
-- </vc-theorems>