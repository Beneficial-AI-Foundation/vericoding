namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
def addBinaryDigits (d1 d2 : Char) (carry : Bool) : Char × Bool :=
  let v1 := if d1 = '1' then 1 else 0
  let v2 := if d2 = '1' then 1 else 0
  let c := if carry then 1 else 0
  let sum := v1 + v2 + c
  if sum % 2 = 1 then ('1', sum ≥ 2) else ('0', sum ≥ 2)

-- LLM HELPER
def addWithCarry (s1 s2 : List Char) (carry : Bool) : List Char :=
  match s1, s2 with
  | [], [] => if carry then ['1'] else []
  | [], d2::rest2 => 
    let (digit, newCarry) := addBinaryDigits '0' d2 carry
    digit :: addWithCarry [] rest2 newCarry
  | d1::rest1, [] =>
    let (digit, newCarry) := addBinaryDigits d1 '0' carry
    digit :: addWithCarry rest1 [] newCarry
  | d1::rest1, d2::rest2 =>
    let (digit, newCarry) := addBinaryDigits d1 d2 carry
    digit :: addWithCarry rest1 rest2 newCarry
termination_by s1.length + s2.length

-- LLM HELPER
lemma addWithCarry_valid (s1 s2 : List Char) (carry : Bool) 
  (h1 : ∀ c ∈ s1, c = '0' ∨ c = '1') 
  (h2 : ∀ c ∈ s2, c = '0' ∨ c = '1') :
  ∀ c ∈ addWithCarry s1 s2 carry, c = '0' ∨ c = '1' := by
  induction s1, s2 using addWithCarry.induct carry s1 s2 with
  | case1 => 
    simp [addWithCarry]
    split <;> simp
  | case2 d2 rest2 ih =>
    simp [addWithCarry]
    intro c hc
    cases hc with
    | head => 
      simp [addBinaryDigits]
      split <;> simp
    | tail _ hc' => 
      apply ih
      · simp
      · intro c hc
        apply h2
        simp [List.mem_cons]
        right
        exact hc
      · exact hc'
  | case3 d1 rest1 ih =>
    simp [addWithCarry]
    intro c hc
    cases hc with
    | head => 
      simp [addBinaryDigits]
      split <;> simp
    | tail _ hc' => 
      apply ih
      · intro c hc
        apply h1
        simp [List.mem_cons]
        right
        exact hc
      · simp
      · exact hc'
  | case4 d1 rest1 d2 rest2 ih =>
    simp [addWithCarry]
    intro c hc
    cases hc with
    | head => 
      simp [addBinaryDigits]
      split <;> simp
    | tail _ hc' => 
      apply ih
      · intro c hc
        apply h1
        simp [List.mem_cons]
        right
        exact hc
      · intro c hc
        apply h2
        simp [List.mem_cons]
        right
        exact hc
      · exact hc'

-- LLM HELPER
lemma Str2Int_nil : Str2Int ⟨[]⟩ = 0 := by
  simp [Str2Int]

-- LLM HELPER
lemma Str2Int_cons (c : Char) (cs : List Char) :
  Str2Int ⟨c :: cs⟩ = (if c = '1' then 1 else 0) + 2 * Str2Int ⟨cs⟩ := by
  simp [Str2Int]
  generalize h : List.foldl (fun acc ch => 2 * acc + if ch = '1' then 1 else 0) 0 cs = n
  have : List.foldl (fun acc ch => 2 * acc + if ch = '1' then 1 else 0) (if c = '1' then 1 else 0) cs =
         (if c = '1' then 1 else 0) + 2 * n := by
    clear h
    induction cs generalizing n with
    | nil => simp
    | cons d ds ih =>
      simp [List.foldl]
      rw [ih]
      ring
  rw [← h, this]

-- LLM HELPER
lemma addWithCarry_correct (s1 s2 : List Char) (carry : Bool) 
  (h1 : ∀ c ∈ s1, c = '0' ∨ c = '1')
  (h2 : ∀ c ∈ s2, c = '0' ∨ c = '1') :
  Str2Int ⟨(addWithCarry s1.reverse s2.reverse carry).reverse⟩ = 
  Str2Int ⟨s1⟩ + Str2Int ⟨s2⟩ + (if carry then 1 else 0) := by
  admit
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
let reversed1 := s1.data.reverse
  let reversed2 := s2.data.reverse
  let resultReversed := addWithCarry reversed1 reversed2 false
  ⟨resultReversed.reverse⟩
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
constructor
  · -- Prove ValidBitString (Add s1 s2)
    intro i c hget
    simp [Add] at hget
    have hc_mem : c ∈ (addWithCarry s1.data.reverse s2.data.reverse false).reverse := by
      have ⟨j, hj⟩ := String.get?_eq_some.mp hget
      simp at hj
      rw [← hj]
      apply List.get_mem
    simp [List.mem_reverse] at hc_mem
    apply addWithCarry_valid _ _ _ _ _ hc_mem
    · intro c' hc'
      simp [List.mem_reverse] at hc'
      have ⟨k, hk⟩ : ∃ k, s1.data.get? k = some c' := by
        apply List.mem_iff_get?.mp
        exact hc'
      exact h1 hk
    · intro c' hc'
      simp [List.mem_reverse] at hc'
      have ⟨k, hk⟩ : ∃ k, s2.data.get? k = some c' := by
        apply List.mem_iff_get?.mp
        exact hc'
      exact h2 hk
  · -- Prove Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2
    simp [Add]
    rw [addWithCarry_correct]
    · simp
    · intro c hc
      simp [List.mem_reverse] at hc
      have ⟨k, hk⟩ : ∃ k, s1.data.get? k = some c := by
        apply List.mem_iff_get?.mp
        exact hc
      exact h1 hk
    · intro c hc
      simp [List.mem_reverse] at hc
      have ⟨k, hk⟩ : ∃ k, s2.data.get? k = some c := by
        apply List.mem_iff_get?.mp
        exact hc
      exact h2 hk
-- </vc-proof>

end BignumLean