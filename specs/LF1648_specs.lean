-- <vc-preamble>
def ConsList.fromArray {α : Type} (arr : Array α) : ConsList α :=
  sorry

def ConsList.toArray {α : Type} (l : ConsList α) : Array α :=
  sorry

def ConsList.filter {α : Type} (l : ConsList α) (p : α → Bool) : ConsList α :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ConsList.map {α β : Type} (l : ConsList α) (f : α → β) : ConsList β :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fromArray_toArray_roundtrip {α : Type} (arr : Array α) :
  let cons := ConsList.fromArray arr
  match cons with
  | ConsList.nil => arr.isEmpty
  | _ => cons.toArray = arr
  := sorry

theorem filter_preserves_valid {α : Type} [BEq α] (arr : Array α) (p : α → Bool) :
  let cons := ConsList.fromArray arr
  match cons with
  | ConsList.nil => True
  | cons =>
    let filtered := cons.filter p
    match filtered with
    | ConsList.nil => ∀ x, x ∈ arr → ¬(p x)
    | filtered =>
      (∀ x, x ∈ filtered.toArray → p x) ∧
      (∀ x, x ∈ filtered.toArray → x ∈ arr) ∧
      (∀ x, x ∈ arr → p x → x ∈ filtered.toArray)
  := sorry

theorem map_applies_function {α β : Type} (arr : Array α) (f : α → β) :
  let cons := ConsList.fromArray arr
  (cons.map f |>.toArray) = arr.map f
  := sorry

theorem map_preserves_length {α β : Type} (arr : Array α) (f : α → β) :
  let cons := ConsList.fromArray arr
  (cons.map f |>.toArray).size = arr.size
  := sorry

theorem operations_independent {α : Type} (arr1 arr2 : Array α) (f : α → α) :
  let cons1 := ConsList.fromArray arr1
  let cons2 := ConsList.fromArray arr2
  match cons1, cons2 with
  | ConsList.nil, _ => True
  | _, ConsList.nil => True
  | cons1, cons2 =>
    let _ := cons1.map f
    cons2.toArray = arr2
  := sorry

theorem successive_operations {α : Type} [BEq α] [OfNat α 1] [OfNat α 2] [Mul α] (arr : Array α) :
  let cons := ConsList.fromArray arr
  match cons with
  | ConsList.nil => True
  | cons =>
    let doubled := cons.map (· * 2)
    match doubled with
    | ConsList.nil => True
    | doubled =>
      let filtered := doubled.filter (fun _ => true)
      match filtered with
      | ConsList.nil => True
      | filtered =>
        let final := filtered.map (· * 1)
        ∀ x, x ∈ final.toArray → x ∈ arr
  := sorry
-- </vc-theorems>