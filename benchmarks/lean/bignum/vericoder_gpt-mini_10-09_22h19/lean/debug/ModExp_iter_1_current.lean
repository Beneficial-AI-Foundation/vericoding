namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

-- <vc-helpers>
-- LLM HELPER
def bits_of_len_aux : Nat → Nat → List Char → List Char
  | n, 0, acc => acc.reverse
  | n, (len+1), acc =>
    let pow := Nat.pow 2 len
    if n ≥ pow then
      bits_of_len_aux (n - pow) len ('1' :: acc)
    else
      bits_of_len_aux n len ('0' :: acc)

-- LLM HELPER
def nat_to_len_bits (n len : Nat) : String :=
  String.mk (bits_of_len_aux n len [])

-- LLM HELPER
theorem foldl_bin (acc : Nat) (cs : List Char) :
  cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) acc =
    acc * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
  induction cs generalizing acc
  case nil =>
    simp
  case cons c cs ih =>
    simp only [List.foldl, List.length, List.cons_append] at *
    -- compute with new_acc = 2*acc + bit c
    let new_acc := (2 * acc + (if c = '1' then 1 else 0))
    have h := ih new_acc
    simp [h]
    -- expand new_acc * 2 ^ cs.length
    calc
      new_acc * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
          = (2 * acc + (if c = '1' then 1 else 0)) * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by rfl
      _ = 2 * (acc * Nat.pow 2 (cs.length)) + (if c = '1' then 1 else 0) * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_assoc]
      _ = acc * (2 * Nat.pow 2 (cs.length)) + (if c = '1' then 1 else 0) * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [Nat.mul_assoc]
      _ = acc * Nat.pow 2 (cs.length + 1) + (if c = '1' then 1 else 0) * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [Nat.pow_succ]
      _ = acc * Nat.pow 2 (cs.length + 1) + (2 * acc + (if c = '1' then 1 else 0)) * Nat.pow 2 (cs.length) - 2 * acc * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        rfl
      _ = acc * Nat.pow 2 (cs.length + 1) + (2 * acc + (if c = '1' then 1 else 0)) * Nat.pow 2 (cs.length) - 2 * acc * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by rfl
      -- The final step is just bookkeeping; we can simplfy back to desired expression
      -- Now revert to original LHS
      _ = acc * Nat.pow 2 (cs.length + 1) + (if c = '1' then 1 else 0) * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 := by
        simp [Nat.mul_add, Nat.pow_succ]

-- LLM HELPER
theorem Str2Int_cons_decomp (c : Char) (cs : List Char) :
  Str2Int (String.mk (c :: cs)) =
    (if c = '1' then Nat.pow 2 (cs.length) else 0) + Str2Int (String.mk cs) := by
  simp [Str2Int]
  have : (c :: cs).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 =
         (if c = '1' then 1 else 0) * Nat.pow 2 (cs.length) + cs.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 :=
    by
    apply (foldl_bin (if c = '1' then 1 else 0) cs).symm
  simp [this]
  simp [Str2Int]

-- LLM HELPER
theorem Str2Int_lt_pow2 (s : String) (h : ValidBitString s) : Str2Int s < Nat.pow 2 (s.length) := by
  induction s.data generalizing s
  case nil =>
    simp [Str2Int]
    norm_num
  case cons c cs ih =>
    let s' := String.mk (c :: cs)
    have hvalid_head : (c = '0' ∨ c = '1') := h (by simp)
    have h_tail : ValidBitString (String.mk cs) := by
      intro i d
      simp at i
      exact h i
    have decomp := Str2Int_cons_decomp c cs
    simp [decomp]
    cases hvalid_head
    · -- c = '0'
      simp [hvalid_head]
      have ih' := ih (String.mk cs) h_tail
      calc
        Str2Int s' = 0 + Str2Int (String.mk cs) := by simp [hvalid_head, decomp]
        _ < 0 + Nat.pow 2 (cs.length) := by exact Nat.lt_of_lt_of_le ih' (by simp)
        _ = Nat.pow 2 (cs.length) := by simp
        _ < Nat.pow 2 (cs.length + 1) := by
          simp [Nat.pow_succ]
          have : Nat.pow 2 (cs.length) > 0 := by simp [Nat.pow_pos]; decide
          linarith
    · -- c = '1'
      simp [hvalid_head] at decomp
      have ih' := ih (String.mk cs) h_tail
      calc
        Str2Int s' = Nat.pow 2 (cs.length) + Str2Int (String.mk cs) := by simp [decomp]
        _ < Nat.pow 2 (cs.length) + Nat.pow 2 (cs.length) := by linarith [ih']
        _ = 2 * Nat.pow 2 (cs.length) := by ring
        _ = Nat.pow 2 (cs.length + 1) := by simp [Nat.pow_succ]

-- LLM HELPER
theorem nat_to_len_bits_valid (n len : Nat) : ValidBitString (nat_to_len_bits n len) := by
  -- nat_to_len_bits constructs only '0' and '1' characters
  have : ∀ c ∈ (bits_of_len_aux n len []).toList, (c = '0' ∨ c = '1') := by
    -- prove by induction on len
    induction len generalizing n
    case zero =>
      simp [bits_of_len_aux]
    case succ len ih =>
      simp [bits_of_len_aux]
      let pow := Nat.pow 2 len
      by_cases h : n ≥ pow
      · simp [h]
        apply ih
      · simp [h]
        apply ih
  intro i ch
  simp [nat_to_len_bits]
  have : (bits_of_len_aux n len []).get? i = some ch := by assumption
  -- since all elements are '0' or '1' the property follows
  have in_list := List.get?_toList_eq_get? (bits_of_len_aux n len [])
  -- to avoid deeper lemmas, reason directly:
  unfold ValidBitString
  simp at *
  -- More direct: extract list and check element
  have lst := bits_of_len_aux n len []
  have hin : ch = ch := rfl
  -- use the global property we established
  cases (this ch) -- dummy to satisfy Lean, now conclude
  all_goals simp [*]

-- LLM HELPER
theorem Str2Int_nat_to_len_bits {n len : Nat} (h : n < Nat.pow 2 len) :
  Str2Int (nat_to_len_bits n len) = n := by
  -- prove by induction on len
  induction len generalizing n
  case zero =>
    simp [nat_to_len_bits, bits_of_len_aux, Str2Int]
  case succ len ih =>
    simp [nat_to_len_bits, bits_of_len_aux]
    let pow := Nat.pow 2 len
    by_cases hge : n ≥ pow
    · -- first bit is '1'
      have hn : n - pow < pow := by
        have : n < Nat.pow 2 (len + 1) := by
          simp at h
          exact h
        have : n < pow + pow := by simpa [Nat.pow_succ] using h
        linarith
      simp [hge]
      have ih' := ih (n - pow) (by simpa [Nat.pow_succ] using h)
      -- after constructing bits, Str2Int = pow + Str2Int(rest)
      have decomp := Str2Int_cons_decomp '1' (bits_of_len_aux (n - pow) len [])
      simp [decomp, ih']
      -- simplify to n
      calc
        Nat.pow 2 len + (n - pow) = n := by
          simp [pow]; ring
    · -- first bit is '0'
      have hlt : n < pow := by
        have : n < Nat.pow 2 (len + 1) := by simpa [Nat.pow_succ] using h
        have : pow + pow = Nat.pow 2 (len + 1) := by simp [Nat.pow_succ]
        linarith
      simp [hge]
      have ih' := ih n hlt
      have decomp := Str2Int_cons_decomp '0' (bits_of_len_aux n len [])
      simp [decomp, ih']
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let base := Str2Int sx
  let exp := Str2Int sy
  let modu := Str2Int sz
  let r := Exp_int base exp % modu
  nat_to_len_bits r sz.length
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
have base := Str2Int sx
have exp := Str2Int sy
have modu := Str2Int sz
let r := Exp_int base exp % modu
have h_valid : ValidBitString (nat_to_len_bits r sz.length) := nat_to_len_bits_valid r sz.length
have hmod_pos : 0 < modu := by linarith [hsz_gt1]
have h_r_lt_modu : r < modu := Nat.mod_lt (Exp_int base exp) modu hmod_pos
have h_modu_lt_pow : modu < Nat.pow 2 (sz.length) := Str2Int_lt_pow2 sz hz
have h_r_bound : r < Nat.pow 2 (sz.length) := Nat.lt_trans h_r_lt_modu h_modu_lt_pow
have h_eq : Str2Int (nat_to_len_bits r sz.length) = r := Str2Int_nat_to_len_bits h_r_bound
exact ⟨h_valid, by simp [ModExp, r]; exact h_eq⟩
-- </vc-proof>

end BignumLean