def numerical_triangle (n: Nat) : String := sorry

def String.splitLines (s : String) : List String := sorry

-- <vc-helpers>
-- </vc-helpers>

def String.allDigits (s : String) : Bool := sorry
def String.toNat (s : String) : Option Nat := sorry

theorem numerical_triangle_increasing_length (n: Nat)
    (h: 1 ≤ n ∧ n ≤ 20) :
    let lines := (numerical_triangle n).splitLines
    lines ≠ [] →
    ∀ i, 1 ≤ i → i < lines.length →
    (lines.get! i).length > (lines.get! (i-1)).length := sorry

theorem numerical_triangle_line_count (n: Nat)
    (h: 1 ≤ n ∧ n ≤ 20) :
    let lines := (numerical_triangle n).splitLines
    lines ≠ [] →
    lines.length = n - 1 := sorry

theorem numerical_triangle_valid_integers (n: Nat)
    (h: 1 ≤ n ∧ n ≤ 20) :
    let lines := (numerical_triangle n).splitLines
    lines ≠ [] →
    ∀ line, line ∈ lines →
    line.allDigits ∧
    (∃ num, line.toNat = some num ∧ num > 0) := sorry

/-
info: '1\n22\n333\n4444'
-/
-- #guard_msgs in
-- #eval numerical_triangle 5

/-
info: '1\n22'
-/
-- #guard_msgs in
-- #eval numerical_triangle 3

/-
info: '1'
-/
-- #guard_msgs in
-- #eval numerical_triangle 2

-- Apps difficulty: introductory
-- Assurance level: unguarded