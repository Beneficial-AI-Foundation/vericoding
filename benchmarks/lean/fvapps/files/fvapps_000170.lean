-- <vc-preamble>
def Even (n : Nat) : Prop := ∃ k, n = 2 * k

def countOdds (xs : List Int) : Nat :=
  xs.foldl (fun acc x => if x % 2 = 1 then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_arrange (arr : List Int) (k : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_arrange_result_type (arr : List Int) (k : Nat) :
  can_arrange arr k = true ∨ can_arrange arr k = false :=
sorry

theorem can_arrange_even_length {arr : List Int} {k : Nat} :
  can_arrange arr k = true → List.length arr % 2 = 0 :=
sorry

theorem can_arrange_k_one {arr : List Int} :
  can_arrange arr 1 = true ↔ List.length arr % 2 = 0 :=
sorry

theorem can_arrange_k_two {arr : List Int} :
  can_arrange arr 2 = true →
  Even (countOdds arr) :=
sorry

theorem can_arrange_empty {k : Nat} :
  can_arrange [] k = true :=
sorry

theorem can_arrange_singleton {x : Int} {k : Nat} :
  can_arrange [x] k = false :=
sorry
-- </vc-theorems>