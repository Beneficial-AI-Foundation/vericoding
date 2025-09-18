-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dontGiveMeFive (s e : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validRange (s e : Int) :
  s ≤ e →
  let result := dontGiveMeFive s e
  (result ≥ 0 ∧ result ≤ e - s + 1) := by
  sorry

theorem fiveDigitCount (s e : Int) :
  s ≤ e →
  dontGiveMeFive s e = Int.ofNat (
    (List.map (Int.ofNat) (List.range (Int.toNat (e - s + 1))))
      |>.map (fun x => x + s)
      |>.filter (fun x => ¬ String.contains (toString (Int.natAbs x)) '5')
      |>.length) := by
  sorry 

theorem emptyRange (s e : Int) :
  s > e →
  dontGiveMeFive s e = 0 := by
  sorry

theorem singleNumber (n : Int) :
  dontGiveMeFive n n = 
    if String.contains (toString (Int.natAbs n)) '5' then 0 else 1 := by
  sorry
-- </vc-theorems>