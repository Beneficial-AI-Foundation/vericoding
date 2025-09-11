namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
def shiftLeft (s : String) : String :=
  s ++ "0"

-- LLM HELPER
lemma shiftLeft_doubles (s : String) (h : ValidBitString s) :
  ValidBitString (shiftLeft s) ∧ Str2Int (shiftLeft s) = 2 * Str2Int s := by
  constructor
  · -- Prove ValidBitString (shiftLeft s)
    intro i c hi
    unfold shiftLeft at hi
    have : (s ++ "0").data = s.data ++ ['0'] := by 
      simp [String.append, String.data]
    rw [String.get?] at hi
    by_cases h_lt : i.val < s.data.length
    · have hs := h
      simp [String.get?] at hs
      have hi' : s.get? i = some c := by
        rw [String.get?]
        simp at hi
        rw [this] at hi
        simp [List.get?_append, h_lt] at hi
        exact hi
      exact hs hi'
    · simp at hi
      rw [this] at hi
      simp [List.get?_append] at hi
      by_cases h_eq : i.val = s.data.length
      · simp [h_eq, not_lt.mp h_lt] at hi
        left
        exact hi
      · have : i.val > s.data.length := Nat.lt_of_le_of_ne (not_lt.mp h_lt) h_eq
        simp [this] at hi
  · -- Prove Str2Int (shiftLeft s) = 2 * Str2Int s
    unfold shiftLeft Str2Int
    have : (s ++ "0").data = s.data ++ ['0'] := by simp [String.append]
    rw [this]
    rw [List.foldl_append]
    simp [List.foldl]
    ring

-- LLM HELPER
def mulHelper (s1 : String) (s2_data : List Char) (acc : String) : String :=
  match s2_data with
  | [] => acc
  | '0' :: rest => mulHelper (shiftLeft s1) rest acc
  | _ :: rest => mulHelper (shiftLeft s1) rest (Add acc s1)
termination_by s2_data.length
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
if s2.isEmpty then
    "0"
  else
    mulHelper s1 s2.data "0"
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Mul
  by_cases h_empty : s2.isEmpty
  · -- Case: s2 is empty
    simp [h_empty]
    constructor
    · intro i c hi
      simp at hi
      by_cases h_eq : i.val = 0
      · simp [h_eq] at hi; left; exact hi
      · simp [h_eq] at hi
    · have : Str2Int s2 = 0 := by
        unfold Str2Int
        have : s2.data = [] := by
          simp [String.isEmpty] at h_empty
          exact List.eq_nil_of_length_eq_zero h_empty
        rw [this]
        simp [List.foldl]
      rw [this]
      simp [Str2Int, List.foldl]
  · -- Case: s2 is not empty
    simp [h_empty]
    -- We need to prove properties about mulHelper
    -- This requires induction on s2.data
    have mul_helper_correct : ∀ (s1_shifted : String) (s2_tail : List Char) (acc : String),
      ValidBitString s1_shifted →
      ValidBitString acc →
      (∀ c, c ∈ s2_tail → (c = '0' ∨ c = '1')) →
      let result := mulHelper s1_shifted s2_tail acc
      ValidBitString result ∧ 
      Str2Int result = Str2Int acc + Str2Int s1_shifted * s2_tail.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 := by
      intro s1_shifted s2_tail
      induction s2_tail with
      | nil => 
        intro acc _ h_acc _
        unfold mulHelper
        simp
        constructor
        · exact h_acc
        · simp [List.foldl]
      | cons hd tl ih =>
        intro acc h_s1 h_acc h_valid
        unfold mulHelper
        have h_hd : hd = '0' ∨ hd = '1' := by
          apply h_valid hd
          simp
        match hd with
        | '0' =>
          have h_tl_valid : ∀ c, c ∈ tl → (c = '0' ∨ c = '1') := by
            intro c h_in
            apply h_valid c
            simp [h_in]
          have h_shift := shiftLeft_doubles s1_shifted h_s1
          have ih_result := ih acc h_shift.1 h_acc h_tl_valid
          constructor
          · exact ih_result.1
          · rw [ih_result.2]
            simp [List.foldl]
            rw [h_shift.2]
            ring
        | _ =>
          have h_tl_valid : ∀ c, c ∈ tl → (c = '0' ∨ c = '1') := by
            intro c h_in
            apply h_valid c
            simp [h_in]
          have h_shift := shiftLeft_doubles s1_shifted h_s1
          have h_add := Add_spec acc s1_shifted h_acc h_s1
          have ih_result := ih (Add acc s1_shifted) h_shift.1 h_add.1 h_tl_valid
          constructor
          · exact ih_result.1
          · rw [ih_result.2, h_add.2, h_shift.2]
            simp [List.foldl]
            cases h_hd with
            | inl h0 => simp [h0]; ring
            | inr h1 => simp [h1]; ring
    
    -- Apply the helper lemma
    have h_s2_valid : ∀ c, c ∈ s2.data → (c = '0' ∨ c = '1') := by
      intro c h_in
      have : ∃ i, s2.data.get? i = some c := List.mem_iff_get?.mp h_in
      obtain ⟨i, hi⟩ := this
      exact h2 (by rw [String.get?_eq_data_get?]; exact hi)
    
    have h_zero_valid : ValidBitString "0" := by
      intro i c hi
      simp at hi
      by_cases h_eq : i.val = 0
      · simp [h_eq] at hi; left; exact hi
      · simp [h_eq] at hi
    
    have result := mul_helper_correct s1 s2.data "0" h1 h_zero_valid h_s2_valid
    constructor
    · exact result.1
    · rw [result.2]
      simp [Str2Int, List.foldl]
-- </vc-proof>

end BignumLean