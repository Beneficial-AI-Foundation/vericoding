def split (s : String) (c : Char) : List String :=
sorry

def vert_mirror (s : String) : String :=
sorry

def hor_mirror (s : String) : String := 
sorry

def oper (f : String → String) (s : String) : String :=
sorry

def reverse_string (s : String) : String :=
sorry

def all_lines_reversed (orig result : List String) : Prop :=
  ∀ i, i < orig.length → result.get! i = reverse_string (orig.get! i)

-- <vc-helpers>
-- </vc-helpers>

def line_lengths_preserved (orig result : List String) : Prop :=
  ∀ i, i < orig.length → (orig.get! i).length = (result.get! i).length

axiom vert_mirror_properties (s : String) :
  let lines := split s '\n'
  let result_lines := split (oper vert_mirror s) '\n'
  lines.length = result_lines.length ∧
  all_lines_reversed lines result_lines ∧
  line_lengths_preserved lines result_lines

axiom hor_mirror_properties (s : String) :
  let lines := split s '\n'
  let result_lines := split (oper hor_mirror s) '\n'
  lines.length = result_lines.length ∧
  result_lines = List.reverse lines

axiom vert_mirror_involution (s : String) :
  oper vert_mirror (oper vert_mirror s) = s

axiom hor_mirror_involution (s : String) :
  oper hor_mirror (oper hor_mirror s) = s

/-
info: 'dcba\nhgfe\nlkji\nponm'
-/
-- #guard_msgs in
-- #eval oper vert_mirror "abcd\nefgh\nijkl\nmnop"

/-
info: 'mnop\nijkl\nefgh\nabcd'
-/
-- #guard_msgs in
-- #eval oper hor_mirror s1

/-
info: 'ba\ndc'
-/
-- #guard_msgs in
-- #eval oper vert_mirror "ab\ncd"

/-
info: 'cd\nab'
-/
-- #guard_msgs in
-- #eval oper hor_mirror s2

-- Apps difficulty: introductory
-- Assurance level: unguarded