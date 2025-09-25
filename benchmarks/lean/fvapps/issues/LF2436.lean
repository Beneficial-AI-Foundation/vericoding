-- <vc-preamble>
def sumSet (s : SetInt) : Int := sorry
def process_set_commands (elements : List Int) (commands : List String) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pop_element_from_set (s : SetInt) : SetInt := sorry
def contains (s : SetInt) (x : Int) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pop_reduces_size (elements : List Int) (h : elements ≠ []) : 
  let s := SetInt.mk elements
  let after_pop := pop_element_from_set s
  List.length after_pop.elements = List.length s.elements - 1 ∧ 
  process_set_commands elements ["pop"] = sumSet after_pop := sorry

theorem remove_vs_discard (elements : List Int) (value : Int) :
  let s := SetInt.mk elements
  let remove_result := process_set_commands elements [s!"remove {value}"]
  let discard_result := process_set_commands elements [s!"discard {value}"]
  if contains s value then
    remove_result = discard_result
  else
    discard_result = sumSet s := sorry

theorem limited_pops (elements : List Int) (num_pops : Nat) 
  (h1 : elements ≠ []) 
  (h2 : List.length elements > num_pops)
  (h3 : num_pops ≤ 3) :
  let commands := List.replicate num_pops "pop"
  let s := SetInt.mk elements
  let result := process_set_commands elements commands
  let final_set := (List.foldl (fun acc _ => pop_element_from_set acc) s commands)
  result = sumSet final_set := sorry
-- </vc-theorems>