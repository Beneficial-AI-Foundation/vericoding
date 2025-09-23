-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_path_and_nest (lst : List Int) (target : Int) : List Int × Int := sorry

theorem find_path_and_nest_result_structure {lst : List Int} {target : Int} 
  (h : lst ≠ []) :
  let result := find_path_and_nest lst target
  result.2 = 0 ∨ result.2 = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_path_and_nest_target_not_found {lst : List Int} {target : Int}
  (h1 : lst ≠ []) 
  (h2 : target ∉ lst) :
  find_path_and_nest lst target = ([], 0) := sorry

theorem find_path_and_nest_target_first {lst : List Int} {target : Int}
  (h1 : lst ≠ []) 
  (h2 : lst.head? = some target) :
  find_path_and_nest lst target = ([0], 1) := sorry

theorem find_path_and_nest_target_later {lst : List Int} {target : Int}
  (h1 : lst ≠ []) 
  (h2 : lst.head? ≠ some target)
  (h3 : target ∈ lst.tail) :
  let result := find_path_and_nest lst target
  result.2 = 1 ∧ 
  result.1.head? = lst.head? ∧
  result.1.tail.all (λ x => x ≥ 0) := sorry

theorem find_path_and_nest_reflexive {lst : List Int}
  (h : lst ≠ []) :
  find_path_and_nest lst (lst.head?.get!) = ([0], 1) := sorry
-- </vc-theorems>