namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  let t := NormalizeBitString s
  ValidBitString t ∧
  t.length > 0 ∧
  (t.length > 1 → t.get? 0 = some '1') ∧
  Str2Int s = Str2Int t

-- <vc-helpers>
-- LLM HELPER
def addBinaryHelper (s1 s2 : List Char) (carry : Nat) : List Char :=
  match s1, s2 with
  | [], [] => if carry = 1 then ['1'] else []
  | [], h2::t2 => 
    let digit2 := if h2 = '1' then 1 else 0
    let sum := digit2 + carry
    (if sum % 2 = 1 then '1' else '0') :: addBinaryHelper [] t2 (sum / 2)
  | h1::t1, [] =>
    let digit1 := if h1 = '1' then 1 else 0
    let sum := digit1 + carry
    (if sum % 2 = 1 then '1' else '0') :: addBinaryHelper t1 [] (sum / 2)
  | h1::t1, h2::t2 =>
    let digit1 := if h1 = '1' then 1 else 0
    let digit2 := if h2 = '1' then 1 else 0
    let sum := digit1 + digit2 + carry
    (if sum % 2 = 1 then '1' else '0') :: addBinaryHelper t1 t2 (sum / 2)
termination_by s1.length + s2.length

-- LLM HELPER
lemma addBinaryHelper_valid (s1 s2 : List Char) (carry : Nat) 
  (h1 : ∀ c ∈ s1, c = '0' ∨ c = '1') 
  (h2 : ∀ c ∈ s2, c = '0' ∨ c = '1')
  (hc : carry ≤ 1) :
  ∀ c ∈ addBinaryHelper s1 s2 carry, c = '0' ∨ c = '1' := by
  induction s1, s2 using addBinaryHelper.induct s1 s2 carry with
  | case1 => 
    simp [addBinaryHelper]
    split <;> simp
  | case2 h2 t2 ih =>
    simp [addBinaryHelper]
    intro c hc'
    cases hc' with
    | head => simp
    | tail _ ht =>
      apply ih
      · simp
      · intro c' hc''
        exact h2 c' (List.mem_cons_of_mem _ hc'')
      · simp; omega
      · exact ht
  | case3 h1 t1 ih =>
    simp [addBinaryHelper]
    intro c hc'
    cases hc' with
    | head => simp
    | tail _ ht =>
      apply ih
      · intro c' hc''
        exact h1 c' (List.mem_cons_of_mem _ hc'')
      · simp
      · simp; omega
      · exact ht
  | case4 h1 t1 h2 t2 ih =>
    simp [addBinaryHelper]
    intro c hc'
    cases hc' with
    | head => simp
    | tail _ ht =>
      apply ih
      · intro c' hc''
        exact h1 c' (List.mem_cons_of_mem _ hc'')
      · intro c' hc''
        exact h2 c' (List.mem_cons_of_mem _ hc'')
      · simp; omega
      · exact ht

-- LLM HELPER
lemma List.mem_get? {α : Type*} {l : List α} {i : Nat} {x : α} :
  l.get? i = some x → x ∈ l := by
  intro h
  induction l generalizing i with
  | nil => simp at h
  | cons hd tl ih =>
    cases i with
    | zero => simp at h; rw [← h]; simp
    | succ j => simp at h; right; exact ih h

-- LLM HELPER  
lemma addBinaryHelper_value (s1 s2 : List Char) (carry : Nat) 
  (h1 : ∀ c ∈ s1, c = '0' ∨ c = '1') 
  (h2 : ∀ c ∈ s2, c = '0' ∨ c = '1')
  (hc : carry ≤ 1) :
  (addBinaryHelper s1 s2 carry).foldr (fun ch acc => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  s1.foldr (fun ch acc => 2 * acc + (if ch = '1' then 1 else 0)) 0 +
  s2.foldr (fun ch acc => 2 * acc + (if ch = '1' then 1 else 0)) 0 + carry := by
  induction s1, s2 using addBinaryHelper.induct s1 s2 carry generalizing carry with
  | case1 => 
    simp [addBinaryHelper]
    split
    · simp; omega
    · simp [*, List.foldr]; omega
  | case2 h2 t2 ih =>
    simp [addBinaryHelper, List.foldr]
    have digit2 := if h2 = '1' then 1 else 0
    have sum := digit2 + carry
    simp only [digit2, sum]
    rw [ih]
    · intro c hc'; exact h2 c (List.mem_cons_of_mem _ hc')
    · omega
    split_ifs <;> omega
  | case3 h1 t1 ih =>
    simp [addBinaryHelper, List.foldr]
    have digit1 := if h1 = '1' then 1 else 0
    have sum := digit1 + carry
    simp only [digit1, sum]
    rw [ih]
    · intro c hc'; exact h1 c (List.mem_cons_of_mem _ hc')
    · omega
    split_ifs <;> omega
  | case4 h1 t1 h2 t2 ih =>
    simp [addBinaryHelper, List.foldr]
    have digit1 := if h1 = '1' then 1 else 0
    have digit2 := if h2 = '1' then 1 else 0
    have sum := digit1 + digit2 + carry
    simp only [digit1, digit2, sum]
    rw [ih]
    · intro c hc'; exact h1 c (List.mem_cons_of_mem _ hc')
    · intro c hc'; exact h2 c (List.mem_cons_of_mem _ hc')
    · omega
    split_ifs <;> omega

-- LLM HELPER
lemma List.foldl_reverse {α β : Type*} (f : β → α → β) (init : β) (l : List α) :
  l.reverse.foldl f init = l.foldr (fun x acc => f acc x) init := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih => simp [ih]
-- </vc-helpers>

-- <vc-spec>
def Add (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
let rev1 := s1.data.reverse
let rev2 := s2.data.reverse
let sumRev := addBinaryHelper rev1 rev2 0
NormalizeBitString ⟨sumRev.reverse⟩
-- </vc-code>

-- <vc-theorem>
theorem Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Add
let rev1 := s1.data.reverse
let rev2 := s2.data.reverse
let sumRev := addBinaryHelper rev1 rev2 0
obtain ⟨valid_norm, len_pos, leading_one, value_preserved⟩ := 
  NormalizeBitString_spec ⟨sumRev.reverse⟩ (by
    intro i c hget
    simp at hget
    have mem_rev : c ∈ sumRev.reverse := List.mem_get? hget
    rw [List.mem_reverse] at mem_rev
    apply addBinaryHelper_valid _ _ _ _ _ _ mem_rev
    · intro c' hc'
      rw [List.mem_reverse] at hc'
      have : ∃ j, s1.data.get? j = some c' := List.mem_iff_get?.mp hc'
      obtain ⟨j, hj⟩ := this
      exact h1 hj
    · intro c' hc'
      rw [List.mem_reverse] at hc'
      have : ∃ j, s2.data.get? j = some c' := List.mem_iff_get?.mp hc'
      obtain ⟨j, hj⟩ := this
      exact h2 hj
    · simp)
constructor
· exact valid_norm
· rw [← value_preserved]
  simp [Str2Int]
  rw [List.foldl_reverse, List.foldl_reverse]
  apply addBinaryHelper_value
  · intro c hc
    rw [List.mem_reverse] at hc
    have : ∃ j, s1.data.get? j = some c := List.mem_iff_get?.mp hc
    obtain ⟨j, hj⟩ := this
    exact h1 hj
  · intro c hc
    rw [List.mem_reverse] at hc
    have : ∃ j, s2.data.get? j = some c := List.mem_iff_get?.mp hc
    obtain ⟨j, hj⟩ := this
    exact h2 hj
  · simp
-- </vc-proof>

end BignumLean