-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compose (f : β → γ) (g : α → β) : α → γ := sorry

theorem numeric_composition (x : Int) :
  let f := (fun x => x + 1)
  let g := (fun x => x * 2)
  compose f g x = f (g x) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_composition (s : String) :
  let f := (fun x => x ++ "!")
  let g := String.toUpper
  compose f g s = f (g s) := sorry

-- Simplified version without List.sum

theorem multiple_args (x : Int) :
  let f := (fun x => x + 1)
  let g := (fun x => x)
  compose f g x = f (g x) := sorry

theorem type_preservation (x : Int) :
  let f := (fun _ => Type)
  let g := toString
  compose f g x = f (g x) := sorry

theorem identity_composition (x : Int) :
  let f := (fun x => x)
  let g := (fun x => x)
  compose f g x = x := sorry

theorem nested_composition (x : Int) :
  let f := (fun x => x + 1)
  let g := (fun x => x * 2)
  let h := (fun x => x - 3)
  compose (compose f g) h x = f (g (h x)) := sorry
-- </vc-theorems>