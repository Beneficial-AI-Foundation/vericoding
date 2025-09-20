-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numerical_triangle (n: Nat) : String :=
sorry

def String.splitLines (s : String) : List String :=
sorry

def String.allDigits (s : String) : Bool :=
sorry

def String.toNat (s : String) : Option Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numerical_triangle_increasing_length (n: Nat)
    (h: 1 ≤ n ∧ n ≤ 20) :
    let lines := (numerical_triangle n).splitLines
    lines ≠ [] →
    ∀ i, 1 ≤ i → i < lines.length →
    (lines.get! i).length > (lines.get! (i-1)).length :=
sorry

theorem numerical_triangle_line_count (n: Nat)
    (h: 1 ≤ n ∧ n ≤ 20) :
    let lines := (numerical_triangle n).splitLines
    lines ≠ [] →
    lines.length = n - 1 :=
sorry

theorem numerical_triangle_valid_integers (n: Nat)
    (h: 1 ≤ n ∧ n ≤ 20) :
    let lines := (numerical_triangle n).splitLines
    lines ≠ [] →
    ∀ line, line ∈ lines →
    line.allDigits ∧
    (∃ num, line.toNat = some num ∧ num > 0) :=
sorry
-- </vc-theorems>