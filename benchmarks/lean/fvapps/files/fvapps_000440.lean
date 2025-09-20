-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isContinuationByte (x : Nat) : Bool :=
  sorry

def countRequiredBytes (firstByte : Nat) : Int :=
  sorry

def validUtf8 (data : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_utf8_property (data : List Nat) (h : ∀ x ∈ data, x ≤ 255) :
  validUtf8 data = true →
  ∃ i : Nat,
    i < data.length ∧
    let required := countRequiredBytes (data.get ⟨i, sorry⟩)
    required ≥ 0 ∧
    i + required < data.length ∧
    ∀ j, i + 1 ≤ j ∧ j ≤ i + required →
      isContinuationByte (data.get ⟨j, sorry⟩) = true :=
sorry

theorem valid_utf8_property_contra (data : List Nat) (h : ∀ x ∈ data, x ≤ 255) :
  validUtf8 data = false →
  ∃ i : Nat,
    i < data.length ∧
    (countRequiredBytes (data.get ⟨i, sorry⟩) < 0 ∨
     i + countRequiredBytes (data.get ⟨i, sorry⟩) ≥ data.length ∨
     ∃ j, i + 1 ≤ j ∧ j ≤ i + countRequiredBytes (data.get ⟨i, sorry⟩) ∧
       isContinuationByte (data.get ⟨j, sorry⟩) = false) :=
sorry

theorem ascii_always_valid (data : List Nat) (h : ∀ x ∈ data, x ≤ 127) :
  validUtf8 data = true :=
sorry

theorem continuation_bytes_invalid (data : List Nat) (h1 : data ≠ [])
    (h2 : ∀ x ∈ data, x ≥ 128 ∧ x ≤ 191) :
  validUtf8 data = false :=
sorry
-- </vc-theorems>