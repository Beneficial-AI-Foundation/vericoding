-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def meeting (rooms : List Char) : String ⊕ Nat := sorry

theorem meeting_first_O {rooms : List Char} :
  rooms.contains 'O' →
  ∃ (n : Nat),
    meeting rooms = Sum.inr n ∧
    rooms.get! n = 'O' ∧ 
    ∀ i, i < n → rooms.get! i = 'X'
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem meeting_no_O {rooms : List Char} :
  rooms ≠ [] →
  (¬ rooms.contains 'O') → 
  meeting rooms = Sum.inl "None available!"
  := sorry

theorem meeting_all_X {rooms : List Char} :
  rooms ≠ [] →
  (∀ x ∈ rooms, x = 'X') →
  meeting rooms = Sum.inl "None available!"
  := sorry

theorem meeting_all_O {rooms : List Char} :
  rooms ≠ [] →
  (∀ x ∈ rooms, x = 'O') →
  meeting rooms = Sum.inr 0
  := sorry
-- </vc-theorems>