-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_int_array (xs : List Int) : Bool := sorry

theorem int_array_property (arr : List Int) : 
  is_int_array arr = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem int_array_from_int_list_property (arr : List Int) : 
  is_int_array arr = true := sorry

theorem not_list_property [Inhabited α] (x : α) :
  is_int_array ([] : List Int) = false := sorry

theorem empty_array_property :
  is_int_array ([] : List Int) = true := sorry
-- </vc-theorems>