-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.size {α} : List α → Nat
  | [] => 0
  | _::xs => 1 + xs.size

def sequence_generator (n k : Nat) : List Int :=
  sorry

def count_positive_prefixes (seq : List Int) : Nat :=
  sorry

def sumList (xs : List Int) : Int :=
  sorry

def Int.abs (i : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_length (n k : Nat) (h1 : n > 0) (h2 : k ≤ 100) :
  (sequence_generator n k).size = n :=
sorry

theorem sequence_elements (n k : Nat) (h1 : n > 0) (h2 : k ≤ 100) (h3 : i < n) :
  let seq := sequence_generator n k
  ∀ i : Nat, i < n → Int.abs (seq.get ⟨i, sorry⟩) = i + 1 :=
sorry

theorem positive_prefix_count (n k : Nat) (h1 : n > 0) (h2 : k ≤ 100) :
  count_positive_prefixes (sequence_generator n k) ≤ min k n :=
sorry

theorem all_positive_case (n : Nat) (h : n > 0) :
  let seq := sequence_generator n n
  (∀ i : Nat, i < n → seq.get ⟨i, sorry⟩ > 0) ∧
  seq = List.map (Int.ofNat ∘ Nat.succ) (List.range n) :=
sorry

theorem all_negative_case (n : Nat) (h : n > 0) :
  let seq := sequence_generator n 0
  (∀ i : Nat, i < n → seq.get ⟨i, sorry⟩ < 0) ∧
  seq = List.map (fun i => -Int.ofNat (i + 1)) (List.range n) :=
sorry
-- </vc-theorems>