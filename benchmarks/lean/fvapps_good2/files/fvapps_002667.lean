-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def custom_christmas_tree (chars: String) (n: Nat) : String :=
sorry

def splitLines (s: String) : List String :=
sorry

def stringLength (s: String) : Nat :=
sorry

def stringTrim (s: String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tree_structure_width (chars: String) (n: Nat) :
  let tree := custom_christmas_tree chars n
  ∀ line ∈ splitLines tree, stringLength line ≤ 2 * n :=
sorry

theorem trunk_structure (chars: String) (n: Nat) :
  let tree := custom_christmas_tree chars n
  let trunk_lines := (splitLines tree).drop n
  (∀ line ∈ trunk_lines, stringTrim line = "|") ∧
  trunk_lines.length = (n-1) / 3 + 1 :=
sorry

theorem total_height (chars: String) (n: Nat) :
  let tree := custom_christmas_tree chars n
  (splitLines tree).length = n + ((n-1) / 3 + 1) :=
sorry

theorem tree_part_nonempty (chars: String) (n: Nat) :
  let tree := custom_christmas_tree chars n
  let tree_part := (splitLines tree).take n
  ∀ line ∈ tree_part, stringTrim line ≠ "" :=
sorry
-- </vc-theorems>