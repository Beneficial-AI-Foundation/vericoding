-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def argsToString (args : List (String ⊕ (List String))) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem args_to_string_non_empty {args : List (String ⊕ (List String))} 
  (h : args ≠ []) : 
  argsToString args ≠ "" :=
sorry 

theorem args_to_string_contains_original_elements {args : List (String ⊕ (List String))}
  (arg : String ⊕ List String)
  (h : arg ∈ args) :
  match arg with
  | Sum.inl s => s.data ⊆ (argsToString args).data 
  | Sum.inr lst => ∀ s ∈ lst, s.data ⊆ (argsToString args).data
  :=
sorry

theorem args_to_string_parts_non_empty {args : List (String ⊕ (List String))} :
  let parts := (argsToString args).splitOn " "
  ∀ p ∈ parts, p ≠ "" ∧ p ≠ " " :=
sorry

theorem args_to_string_parts_exist {args : List (String ⊕ (List String))}
  (h : args ≠ []) :
  let parts := (argsToString args).splitOn " " 
  parts ≠ [] :=
sorry
-- </vc-theorems>