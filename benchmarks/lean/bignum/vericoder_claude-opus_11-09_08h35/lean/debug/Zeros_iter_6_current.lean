namespace BignumLean

def AllZero (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, s.get? i = some '0'

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
lemma String.mk_replicate_get (c : Char) (n : Nat) (i : Nat) :
    (String.mk (List.replicate n c)).get? i = if i < n then some c else none := by
  simp [String.get?]
  split
  · next h =>
    have : i < (List.replicate n c).length := by simp [List.length_replicate]; exact h
    simp [List.getElem?_eq_some, this, List.getElem_replicate, h]
  · next h =>
    have : ¬(i < (List.replicate n c).length) := by simp [List.length_replicate]; exact h
    simp [List.getElem?_eq_none, this]

-- LLM HELPER  
lemma foldl_replicate_zero (n : Nat) :
    List.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 (List.replicate n '0') = 0 := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih =>
    simp [List.replicate_succ, List.foldl_cons, ih]

-- LLM HELPER
lemma String.length_mk_replicate (c : Char) (n : Nat) :
    (String.mk (List.replicate n c)).length = n := by
  simp [String.length, List.length_replicate]
-- </vc-helpers>

-- <vc-spec>
def Zeros (n : Nat) : String :=
-- </vc-spec>
-- <vc-code>
String.mk (List.replicate n '0')
-- </vc-code>

-- <vc-theorem>
theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s := by
-- </vc-theorem>
-- <vc-proof>
simp [Zeros]
  constructor
  · -- Prove length = n
    exact String.length_mk_replicate '0' n
  constructor
  · -- Prove ValidBitString
    intro i c h
    rw [String.mk_replicate_get] at h
    split_ifs at h with hi
    · injection h with h'
      simp [h']
    · contradiction
  constructor
  · -- Prove Str2Int s = 0
    simp [Str2Int]
    exact foldl_replicate_zero n
  · -- Prove AllZero
    cases n with
    | zero => 
      left
      simp [String.length, List.replicate]
    | succ n =>
      right
      intro i
      rw [String.mk_replicate_get]
      split_ifs with hi
      · rfl
      · rfl
-- </vc-proof>

end BignumLean