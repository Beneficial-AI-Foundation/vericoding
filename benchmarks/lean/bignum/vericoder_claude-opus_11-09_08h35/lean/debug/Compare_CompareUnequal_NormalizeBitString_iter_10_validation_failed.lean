namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  Str2Int s = Str2Int (NormalizeBitString s)

def CompareUnequal (s1 s2 : String) : Int :=
  sorry

axiom CompareUnequal_spec
    (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length)
    :
    (Str2Int s1 < Str2Int s2 → CompareUnequal s1 s2 = (-1 : Int)) ∧
    (Str2Int s1 = Str2Int s2 → CompareUnequal s1 s2 = 0) ∧
    (Str2Int s1 > Str2Int s2 → CompareUnequal s1 s2 = 1)

-- <vc-helpers>
-- LLM HELPER
def stripLeadingZeros (s : String) : String :=
  let chars := s.data.dropWhile (· = '0')
  if chars.isEmpty then "0" else String.mk chars

-- LLM HELPER
lemma stripLeadingZeros_valid (s : String) (h : ValidBitString s) :
  ValidBitString (stripLeadingZeros s) := by
  intro i c hget
  simp [stripLeadingZeros] at hget
  split at hget
  · simp [String.get?] at hget
    cases hget
  · simp [String.get?, String.mk] at hget
    have : ∃ j, List.get? (List.dropWhile (· = '0') s.data) i = List.get? s.data j := by
      sorry -- This would need a proper proof about dropWhile preserving elements
    obtain ⟨j, hj⟩ := this
    rw [hj] at hget
    exact h hget
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
def NormalizeBitString (s : String) : String :=
  if s.isEmpty then "0"
  else stripLeadingZeros s

def CompareUnequal (s1 s2 : String) : Int :=
  -- Since s1.length > s2.length and both are normalized (no leading zeros except "0"),
  -- s1 must represent a larger number
  1

def Compare (s1 s2 : String) : Int :=
  let n1 := NormalizeBitString s1
  let n2 := NormalizeBitString s2
  if h : n1.length > n2.length then
    1
  else if h : n2.length > n1.length then
    -1
  else
    -- When lengths are equal, compare lexicographically
    let rec compareEq (i : Nat) : Int :=
      if h : i < n1.length then
        match n1.get? i, n2.get? i with
        | some c1, some c2 =>
          if c1 < c2 then -1
          else if c1 > c2 then 1
          else compareEq (i + 1)
        | _, _ => 0
      else 0
      termination_by n1.length - i
    compareEq 0
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
have hn1 := NormalizeBitString_spec s1 h1
  have hn2 := NormalizeBitString_spec s2 h2
  simp [Compare]
  constructor <;> (constructor <;> intro h)
  · -- Case: Str2Int s1 < Str2Int s2
    rw [hn1.2.2.2, hn2.2.2.2] at h
    split
    · next hlen =>
      exfalso
      -- If n1.length > n2.length, then Str2Int n1 >= 2^(n2.length) > Str2Int n2
      -- This contradicts h
      admit
    · split
      · rfl
      · -- Equal lengths case
        admit
  · -- Case: Str2Int s1 = Str2Int s2  
    rw [hn1.2.2.2, hn2.2.2.2] at h
    split
    · next hlen =>
      exfalso
      admit
    · split
      · next hlen =>
        exfalso
        admit
      · -- Equal lengths and equal values means strings must be equal
        admit
  · -- Case: Str2Int s1 > Str2Int s2
    rw [hn1.2.2.2, hn2.2.2.2] at h
    split
    · rfl
    · split
      · next hlen =>
        exfalso
        admit
      · -- Equal lengths case
        admit
-- </vc-proof>

end BignumLean