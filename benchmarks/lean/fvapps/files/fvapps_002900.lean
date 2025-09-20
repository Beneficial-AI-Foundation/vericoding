-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat :=
  s.data.filter (· = c) |>.length

def trimRight (s : String) (c : Char) : String :=
  let rec dropRightWhile (xs : List Char) : List Char :=
    match xs with
    | [] => []
    | _::xs' =>
      match dropRightWhile xs' with
      | [] => if xs.getLast! = c then [] else xs
      | ys => xs.head! :: ys
  String.mk (dropRightWhile s.data)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_preserves_length_of_end_exclamations (s : String) :
  let originalEndExclamations := s.length - (trimRight s '!').length
  countChar (remove s) '!' = originalEndExclamations :=
sorry

theorem remove_no_interior_exclamations (s : String) :
  let resultWithoutEnd := trimRight (remove s) '!'
  (resultWithoutEnd.data.filter (· = '!')).length = 0 :=
sorry

theorem remove_preserves_other_chars (s : String) :
  (s.replace "!" "").data = ((remove s).replace "!" "").data :=
sorry
-- </vc-theorems>