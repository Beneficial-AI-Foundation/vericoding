-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeat_it (s : String) (n : Nat) : String := sorry

theorem repeat_it_length (s : String) (n : Nat) : 
  (repeat_it s n).length = s.length * n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeat_it_equals_repeat (s : String) (n : Nat) :
  repeat_it s n = String.join (List.replicate n s) := sorry

theorem repeat_it_empty_string (n : Nat) :
  repeat_it "" n = "" := sorry

theorem repeat_it_non_string_int (x : Int) (n : Nat) :
  repeat_it (toString x) n = "Not a string" := sorry

theorem repeat_it_non_string_float (x : Float) (n : Nat) :
  repeat_it (toString x) n = "Not a string" := sorry

theorem repeat_it_non_string_list {α : Type} [ToString α] (xs : List α) (n : Nat) :
  repeat_it (toString xs) n = "Not a string" := sorry
-- </vc-theorems>