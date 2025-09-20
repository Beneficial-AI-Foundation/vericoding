-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isVowel (c : Char) : Bool := sorry
def nicknameGenerator (name : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nickname_length (name : String) 
  (h1 : name.length ≥ 4) 
  (h2 : ∀ c ∈ name.data, c.isAlpha) :
  let nickname := nicknameGenerator name
  let h3 : 1 < name.data.length := by {
    have : name.data.length = name.length := rfl
    simp [this] at h1
    exact Nat.lt_of_lt_of_le (by simp) h1
  }
  nickname.length = if isVowel (name.data[1]'h3) then 4 else 3 := sorry

theorem nickname_prefix (name : String)
  (h1 : name.length ≥ 4)
  (h2 : ∀ c ∈ name.data, c.isAlpha) :
  let nickname := nicknameGenerator name
  nickname.take 3 = name.take 3 := sorry

theorem short_name_error (name : String)
  (h : name.length ≤ 3) :
  nicknameGenerator name = "Error: Name too short" := sorry
-- </vc-theorems>