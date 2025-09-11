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
theorem addWithCarry_valid (s1 s2 : List Char) (carry : Bool) 
  (h1 : ∀ c ∈ s1, c = '0' ∨ c = '1') 
  (h2 : ∀ c ∈ s2, c = '0' ∨ c = '1') :
  ∀ c ∈ addWithCarry s1 s2 carry, c = '0' ∨ c = '1' := by
  induction s1 generalizing s2 carry with
  | nil =>
    induction s2 generalizing carry with
    | nil =>
      simp [addWithCarry]
      split <;> simp
    | cons d2 rest2 ih =>
      simp [addWithCarry]
      constructor
      · simp [addBinaryDigits]
        split <;> simp
      · apply ih
        intro c hc
        apply h2
        simp [List.mem_cons]
        right
        exact hc
  | cons d1 rest1 ih1 =>
    cases s2 with
    | nil =>
      simp [addWithCarry]
      constructor
      · simp [addBinaryDigits]
        split <;> simp
      · apply ih1
        · intro c hc
          apply h1
          simp [List.mem_cons]
          right
          exact hc
        · simp
    | cons d2 rest2 =>
      simp [addWithCarry]
      constructor
      · simp [addBinaryDigits]
        split <;> simp
      · apply ih1
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

-- LLM HELPER  
def Str2IntRev (l : List Char) : Nat :=
  l.foldr (fun ch acc => acc * 2 + if ch = '1' then 1 else 0) 0

-- LLM HELPER
theorem Str2Int_eq_Str2IntRev_reverse (s : String) :
  Str2Int s = Str2IntRev s.data.reverse := by
  simp [Str2Int, Str2IntRev]
  generalize s.data = l
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [List.foldl, List.foldr, List.reverse]
    rw [← ih]
    clear ih
    generalize List.foldl (fun acc ch => 2 * acc + if ch = '1' then 1 else 0) 0 t = n
    induction t generalizing n with
    | nil => 
      simp [List.foldl, List.foldr]
      ring
    | cons h' t' _ =>
      simp [List.foldl, List.foldr]
      ring

-- LLM HELPER
theorem addWithCarry_correct (s1 s2 : List Char) (carry : Bool) :
  Str2IntRev (addWithCarry s1 s2 carry) = 
  Str2IntRev s1 + Str2IntRev s2 + if carry then 1 else 0 := by
  induction s1 generalizing s2 carry with
  | nil =>
    induction s2 generalizing carry with
    | nil =>
      simp [addWithCarry, Str2IntRev]
      split <;> simp
    | cons d2 rest2 ih =>
      simp [addWithCarry, Str2IntRev]
      simp [addBinaryDigits]
      by_cases hcarry : carry <;> by_cases hd2 : d2 = '1' <;> simp [hcarry, hd2] at * <;> rw [ih] <;> ring
  | cons d1 rest1 ih1 =>
    cases s2 with
    | nil =>
      simp [addWithCarry, Str2IntRev]
      simp [addBinaryDigits]
      by_cases hcarry : carry <;> by_cases hd1 : d1 = '1' <;> simp [hcarry, hd1] at * <;> rw [ih1] <;> ring
    | cons d2 rest2 =>
      simp [addWithCarry, Str2IntRev]
      simp [addBinaryDigits]
      by_cases hcarry : carry <;> by_cases hd1 : d1 = '1' <;> by_cases hd2 : d2 = '1' <;> 
        simp [hcarry, hd1, hd2] at * <;> rw [ih1] <;> ring

-- LLM HELPER
theorem get_mem {l : List Char} {i : Nat} {x : Char} :
  l.get? i = some x → x ∈ l := by
  intro h
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => 
      simp at h
      rw [← h]
      simp
    | succ i' =>
      simp at h
      right
      exact ih h
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
    apply get_mem
    convert hget
    rfl
  simp [List.mem_reverse] at hc_mem
  apply addWithCarry_valid
  · intro c' hc'
    simp [List.mem_reverse] at hc'
    have : ∃ j, s1.data.get? j = some c' := List.mem_iff_get?.mp hc'
    obtain ⟨j, hj⟩ := this
    apply h1
    exact hj
  · intro c' hc'
    simp [List.mem_reverse] at hc'
    have : ∃ j, s2.data.get? j = some c' := List.mem_iff_get?.mp hc'
    obtain ⟨j, hj⟩ := this
    apply h2
    exact hj
  · exact hc_mem
· -- Prove Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2
  simp [Add]
  rw [Str2Int_eq_Str2IntRev_reverse, Str2Int_eq_Str2IntRev_reverse, Str2Int_eq_Str2IntRev_reverse]
  simp [List.reverse_reverse]
  rw [addWithCarry_correct]
  simp
-- </vc-proof>

end BignumLean