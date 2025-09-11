namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

-- <vc-helpers>
-- LLM HELPER
theorem Str2Int_push_zero (s : String) : Str2Int (s.push '0') = 2 * Str2Int s := by
  -- unfold definitions and use list foldl on appended singleton
  cases s with
  | mk data =>
    dsimp [Str2Int]
    -- (String.mk (data ++ ['0'])).data is definitionally data ++ ['0']
    -- use List.foldl_append to split the foldl over the appended element
    have : (data ++ ['0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
      = (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ['0'] := by
      rfl
    rw [this]
    -- foldl over single element applies the function once
    simp [List.foldl]
    -- conclude
    rfl

-- LLM HELPER
theorem ValidBitString_push (s : String) (hs : ValidBitString s) : ValidBitString (s.push '0') := by
  intro i c h
  cases s with
  | mk data =>
    dsimp [String.push] at h
    -- data ++ ['0'] .get? i is either from data or the last element
    have := List.get?_append data ['0'] i
    dsimp [List.get?] at this
    -- use the general lemma to analyze the two cases
    simp at this
    -- rewrite the specific equality to reason by cases on i < data.length
    have : (data ++ ['0']).get? i = if (i < data.length) then data.get? i else (['0'] : List Char).get? (i - data.length) := by
      rw [List.get?_append]
    rw [this] at h
    by_cases hi : i < data.length
    · simp [hi] at h
      injection h with hcc
      specialize hs (by
        -- rebuild the corresponding get? for original string
        have : (String.mk data).get? i = data.get? i := rfl
        show (String.mk data).get? i = some hcc
        rw [this]
        exact h
      )
      exact hs
    · -- i >= data.length, then the only possible some is when i = data.length and the element is '0'
      simp [hi] at h
      have : (['0'] : List Char).get? (i - data.length) = some c := h
      -- compute index: the singleton has length 1, so i - data.length must be 0
      have : i = data.length := by
        -- from get? some on singleton, index must be 0
        have : (['0'] : List Char).get? (i - data.length) = some '0' := by
          -- singleton get? only returns some '0' at index 0
          have : (['0'] : List Char).get? (i - data.length) = some c := h
          cases (i - data.length) with
          | zero => simp at this; exact this
          | succ _ => simp at this; contradiction
        -- now show i - data.length = 0
        cases (i
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
theorem Str2Int_push_zero (s : String) : Str2Int (s.push '0') = 2 * Str2Int s := by
  -- unfold definitions and use list foldl on appended singleton
  cases s with
  | mk data =>
    dsimp [Str2Int]
    -- (String.mk (data ++ ['0'])).data is definitionally data ++ ['0']
    -- use List.foldl_append to split the foldl over the appended element
    have : (data ++ ['0']).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
      = (List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 data).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) ['0'] := by
      rfl
    rw [this]
    -- foldl over single element applies the function once
    simp [List.foldl]
    -- conclude
    rfl

-- LLM HELPER
theorem ValidBitString_push (s : String) (hs : ValidBitString s) : ValidBitString (s.push '0') := by
  intro i c h
  cases s with
  | mk data =>
    dsimp [String.push] at h
    -- data ++ ['0'] .get? i is either from data or the last element
    have := List.get?_append data ['0'] i
    dsimp [List.get?] at this
    -- use the general lemma to analyze the two cases
    simp at this
    -- rewrite the specific equality to reason by cases on i < data.length
    have : (data ++ ['0']).get? i = if (i < data.length) then data.get? i else (['0'] : List Char).get? (i - data.length) := by
      rw [List.get?_append]
    rw [this] at h
    by_cases hi : i < data.length
    · simp [hi] at h
      injection h with hcc
      specialize hs (by
        -- rebuild the corresponding get? for original string
        have : (String.mk data).get? i = data.get? i := rfl
        show (String.mk data).get? i = some hcc
        rw [this]
        exact h
      )
      exact hs
    · -- i >= data.length, then the only possible some is when i = data.length and the element is '0'
      simp [hi] at h
      have : (['0'] : List Char).get? (i - data.length) = some c := h
      -- compute index: the singleton has length 1, so i - data.length must be 0
      have : i = data.length := by
        -- from get? some on singleton, index must be 0
        have : (['0'] : List Char).get? (i - data.length) = some '0' := by
          -- singleton get? only returns some '0' at index 0
          have : (['0'] : List Char).get? (i - data.length) = some c := h
          cases (i - data.length) with
          | zero => simp at this; exact this
          | succ _ => simp at this; contradiction
        -- now show i - data.length = 0
        cases (i
-- </vc-code>

end BignumLean