-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search (arr : List Int) (target : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem search_returns_valid_index (nums : List Int) (target : Int) 
    (h1 : nums.length > 0)
    (h2 : ∀ (i j : Fin nums.length), i.val < j.val → nums.get i < nums.get j)
    (h3 : ∀ (i j : Fin nums.length), i ≠ j → nums.get i ≠ nums.get j) :
    let rotatePoint := nums.length / 2
    let rotated := nums.drop rotatePoint ++ nums.take rotatePoint
    let result := search rotated target
    (rotated.contains target → 
      result ≥ 0 ∧ result < rotated.length ∧ 
      ∃ (idx : Fin rotated.length), idx.val = result ∧ rotated.get idx = target) ∧
    (¬rotated.contains target → result = -1) :=
  sorry

theorem search_finds_all_elements (nums : List Int) 
    (h1 : nums.length > 0)
    (h2 : ∀ (i j : Fin nums.length), i.val < j.val → nums.get i < nums.get j)
    (h3 : ∀ (i j : Fin nums.length), i ≠ j → nums.get i ≠ nums.get j) :
    let rotatePoint := nums.length / 2
    let rotated := nums.drop rotatePoint ++ nums.take rotatePoint
    ∀ (i : Fin rotated.length), search rotated (rotated.get i) = i.val :=
  sorry

theorem search_edge_cases_empty :
  search [] 1 = -1 := 
  sorry

theorem search_edge_cases_singleton_found : 
  search [1] 1 = 0 :=
  sorry

theorem search_edge_cases_singleton_not_found :
  search [1] 2 = -1 :=
  sorry

theorem search_edge_cases_pair_first :
  search [1, 2] 1 = 0 :=
  sorry

theorem search_edge_cases_pair_rotated :
  search [2, 1] 1 = 1 :=
  sorry

theorem search_edge_cases_triple :
  search [1, 2, 3] 2 = 1 :=
  sorry
-- </vc-theorems>