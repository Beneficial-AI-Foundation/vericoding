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
termination_by (s1.length + s2.length)

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
    intro c hc
    cases hc with
    | head => simp
    | tail _ ht =>
      apply ih
      · simp
      · intro c' hc'
        exact h2 c' (List.mem_cons_of_mem _ hc')
      · simp; omega
      · exact ht
  | case3 h1 t1 ih =>
    simp [addBinaryHelper]
    intro c hc
    cases hc with
    | head => simp
    | tail _ ht =>
      apply ih
      · intro c' hc'
        exact h1 c' (List.mem_cons_of_mem _ hc')
      · simp
      · simp; omega
      · exact ht
  | case4 h1 t1 h2 t2 ih =>
    simp [addBinaryHelper]
    intro c hc
    cases hc with
    | head => simp
    | tail _ ht =>
      apply ih
      · intro c' hc'
        exact h1 c' (List.mem_cons_of_mem _ hc')
      · intro c' hc'
        exact h2 c' (List.mem_cons_of_mem _ hc')
      · simp; omega
      · exact ht

-- LLM HELPER
lemma str2int_addBinaryHelper (s1 s2 : List Char) (carry : Nat)
  (h1 : ∀ c ∈ s1, c = '0' ∨ c = '1')
  (h2 : ∀ c ∈ s2, c = '0' ∨ c = '1')
  (hc : carry ≤ 1) :
  (addBinaryHelper s1 s2 carry).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
  s1.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 +
  s2.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 + carry := by
  induction s1, s2 using addBinaryHelper.induct s1 s2 carry generalizing carry with
  | case1 =>
    simp [addBinaryHelper]
    split
    · simp [List.foldl]
    · simp [List.foldl]; omega
  | case2 h2 t2 ih =>
    simp [addBinaryHelper, List.foldl]
    have : (if h2 = '1' then 1 else 0) + carry < 2 := by
      cases' h2 c mem : h2 <;> simp at mem <;> simp [mem] <;> omega
    conv => rhs; rw [← ih [] (fun _ h => False.elim h) (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) (by omega)]
    simp [List.foldl]
    split <;> simp <;> omega
  | case3 h1 t1 ih =>
    simp [addBinaryHelper, List.foldl]
    have : (if h1 = '1' then 1 else 0) + carry < 2 := by
      cases' h1 c mem : h1 <;> simp at mem <;> simp [mem] <;> omega
    conv => rhs; rw [← ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) (fun _ h => False.elim h) (by omega)]
    simp [List.foldl]
    split <;> simp <;> omega
  | case4 h1 t1 h2 t2 ih =>
    simp [addBinaryHelper, List.foldl]
    have : (if h1 = '1' then 1 else 0) + (if h2 = '1' then 1 else 0) + carry < 4 := by
      cases' h1 c1 mem1 : h1 <;> simp at mem1 <;> simp [mem1] <;>
      cases' h2 c2 mem2 : h2 <;> simp at mem2 <;> simp [mem2] <;> omega
    conv => rhs; rw [← ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) 
                          (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) (by omega)]
    simp [List.foldl]
    split <;> simp <;> omega
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
let intermediate := ⟨(addBinaryHelper s1.data.reverse s2.data.reverse 0).reverse⟩
have valid_intermediate : ValidBitString intermediate := by
  intro i c hget
  simp [ValidBitString, intermediate] at *
  have : c ∈ (addBinaryHelper s1.data.reverse s2.data.reverse 0).reverse := by
    rw [List.mem_reverse]
    exact List.get?_mem (addBinaryHelper s1.data.reverse s2.data.reverse 0) hget
  rw [List.mem_reverse] at this
  apply addBinaryHelper_valid
  · intro c' hc'
    rw [List.mem_reverse] at hc'
    exact h1 (List.get?_index_of_mem _ hc') _ (List.get?_eq_of_mem _ hc')
  · intro c' hc'
    rw [List.mem_reverse] at hc'
    exact h2 (List.get?_index_of_mem _ hc') _ (List.get?_eq_of_mem _ hc')
  · simp
  · exact this
obtain ⟨valid_result, len_pos, leading_one, value_preserved⟩ := NormalizeBitString_spec intermediate valid_intermediate
constructor
· exact valid_result
· simp [Str2Int, intermediate] at value_preserved
  rw [value_preserved]
  simp [Str2Int]
  rw [List.foldl_reverse, List.foldl_reverse, List.foldl_reverse]
  simp [List.foldr]
  rw [str2int_addBinaryHelper]
  · simp
  · intro c hc
    exact h1 _ c (List.get?_eq_of_mem _ hc)
  · intro c hc
    exact h2 _ c (List.get?_eq_of_mem _ hc)
  · simp
-- </vc-proof>

end BignumLean