-- <vc-helpers>
-- </vc-helpers>

def compose (f : β → γ) (g : α → β) : α → γ := sorry

theorem numeric_composition (x : Int) :
  let f := (fun x => x + 1)
  let g := (fun x => x * 2)
  compose f g x = f (g x) := sorry

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

/-
info: 7
-/
-- #guard_msgs in
-- #eval fn 3

/-
info: 'HELLO!'
-/
-- #guard_msgs in
-- #eval fn "hello"

/-
info: 6
-/
-- #guard_msgs in
-- #eval fn 1 2 3

-- Apps difficulty: introductory
-- Assurance level: unguarded