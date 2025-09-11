namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

-- <vc-helpers>
-- LLM HELPER
def getBit (s : String) (i : Nat) : Bool :=
  if h : i < s.length then
    s.get ⟨i, h⟩ = '1'
  else false

-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc else
        aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    aux n ""

-- LLM HELPER
def ModExpImpl (base : Nat) (exp : Nat) (modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if exp = 0 then 1 % modulus
  else
    let rec aux (b : Nat) (e : Nat) (acc : Nat) : Nat :=
      if e = 0 then acc
      else if e % 2 = 1 then
        aux ((b * b) % modulus) (e / 2) ((acc * b) % modulus)
      else
        aux ((b * b) % modulus) (e / 2) acc
    aux (base % modulus) exp 1
termination_by aux _ e _ => e

-- LLM HELPER
lemma ValidBitString_Int2Str (n : Nat) : ValidBitString (Int2Str n) := by
  intro i c hc
  unfold Int2Str at hc
  split at hc
  · simp at hc
    cases hc.symm with
    | refl => exact Or.inl rfl
  · simp at hc
    generalize haux : (let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc else
        aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
      aux n "") = result at hc
    have : ∀ m acc i c, (let rec aux (m : Nat) (acc : String) : String :=
      if m = 0 then acc else
        aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
      aux m acc).get? i = some c → c = '0' ∨ c = '1' := by
      intro m acc
      induction m using Nat.strong_induction_on generalizing acc with
      | _ m ih =>
        intro i c hget
        simp at hget
        split at hget
        · assumption
        · rename_i hm
          have := ih (m / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by norm_num)) _ i c
          apply this
          exact hget
    exact this n "" i c (haux ▸ hc)

-- LLM HELPER
lemma ModExpImpl_spec (base exp modulus : Nat) (hmod : modulus > 0) :
  ModExpImpl base exp modulus = Exp_int base exp % modulus := by
  unfold ModExpImpl
  split
  · contradiction
  · split
    · simp [Exp_int]
    · have : ∀ b e acc,
        (let rec aux (b : Nat) (e : Nat) (acc : Nat) : Nat :=
          if e = 0 then acc
          else if e % 2 = 1 then
            aux ((b * b) % modulus) (e / 2) ((acc * b) % modulus)
          else
            aux ((b * b) % modulus) (e / 2) acc
        aux b e acc) = (acc * Exp_int b e) % modulus := by
        intro b e
        induction e using Nat.strong_induction_on generalizing b with
        | _ e ih =>
          intro acc
          simp
          split
          · simp [Exp_int]
          · split
            · rename_i he_odd he_pos
              have e_pos : e > 0 := Nat.pos_of_ne_zero he_pos
              have : e / 2 < e := Nat.div_lt_self e_pos (by norm_num)
              rw [ih (e / 2) this ((b * b) % modulus) ((acc * b) % modulus)]
              have exp_rec : Exp_int b e = b * Exp_int (b * b) (e / 2) := by
                clear ih this
                induction e using Nat.strong_induction_on generalizing b with
                | _ e ih =>
                  unfold Exp_int
                  split
                  · omega
                  · rename_i he_pos
                    have : e % 2 = 1 := he_odd
                    have : ∃ k, e = 2 * k + 1 := Nat.odd_iff_exists_bit1.mp ⟨k, by omega⟩
                    obtain ⟨k, hk⟩ := this
                    rw [hk]
                    simp [Nat.add_sub_cancel]
                    ring_nf
                    have : k = (2 * k + 1) / 2 := by omega
                    rw [← this]
                    rfl
              rw [exp_rec]
              ring_nf
              rw [Nat.mul_mod, Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
              ring_nf
              · omega
            · rename_i he_even he_pos
              have e_pos : e > 0 := Nat.pos_of_ne_zero he_pos
              have : e / 2 < e := Nat.div_lt_self e_pos (by norm_num)
              rw [ih (e / 2) this ((b * b) % modulus) acc]
              have exp_rec : Exp_int b e = Exp_int (b * b) (e / 2) := by
                clear ih this
                induction e using Nat.strong_induction_on generalizing b with
                | _ e ih =>
                  unfold Exp_int
                  split
                  · omega
                  · rename_i he_pos
                    have : e % 2 = 0 := he_even
                    have : ∃ k, e = 2 * k := Nat.even_iff_two_dvd.mp ⟨k, by omega⟩
                    obtain ⟨k, hk⟩ := this
                    rw [hk]
                    simp [Nat.mul_sub_cancel]
                    have : k = (2 * k) / 2 := by omega
                    rw [← this]
                    ring_nf
                    rfl
              rw [exp_rec]
      rw [this (base % modulus) exp 1]
      simp

-- LLM HELPER
lemma Str2Int_Int2Str (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str
  split
  · simp [Str2Int, String.data]
  · have : ∀ m acc,
      Str2Int (let rec aux (m : Nat) (acc : String) : String :=
        if m = 0 then acc else
          aux (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
        aux m acc) = m * Str2Int acc + m % (2^(String.length acc)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc
        simp
        split
        · simp
        · rename_i hm
          have : m / 2 < m := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by norm_num)
          rw [ih (m / 2) this]
          unfold Str2Int
          simp [String.data, String.append]
          split
          · simp [List.foldl_cons, List.foldl_append]
            ring_nf
            omega
          · simp [List.foldl_cons, List.foldl_append]
            ring_nf
            omega
    simp at this
    specialize this n ""
    simp [Str2Int, String.data] at this
    exact this
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
Int2Str (ModExpImpl (Str2Int sx) (Str2Int sy) (Str2Int sz))
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
constructor
· apply ValidBitString_Int2Str
· rw [Str2Int_Int2Str]
  exact ModExpImpl_spec (Str2Int sx) (Str2Int sy) (Str2Int sz) hsz_gt1
-- </vc-proof>

end BignumLean