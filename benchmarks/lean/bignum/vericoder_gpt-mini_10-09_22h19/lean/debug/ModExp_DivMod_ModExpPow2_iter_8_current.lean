namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

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
/- nat_to_bin_list: produce a list of binary chars ('0'/'1') representing n in binary,
   most-significant bit first. Implemented with well-founded recursion on n. -/
def nat_to_bin_list : Nat → List Char :=
  WellFounded.fix (measure_wf id) fun n rec =>
    if h0 : n = 0 then
      ['0']
    else if h1 : n = 1 then
      ['1']
    else
      let hn : 0 < n := Nat.pos_of_ne_zero h0
      let pf : (n / 2) < n := Nat.div_lt_self hn
      let d := if n % 2 = 1 then '1' else '0'
      (rec (n / 2) pf) ++ [d]

-- LLM HELPER
def nat_to_bin_string (n : Nat) : String :=
  String.mk (nat_to_bin_list n)

-- LLM HELPER
/-- If a predicate holds for every element of a list (List.All), then any element obtained
    by List.get? also satisfies the predicate. -/
theorem All_of_get?_of_All {α : Type} {p : α → Prop} {l : List α} :
  List.All p l → ∀ {i x}, l.get? i = some x → p x := by
  intro Hall
  induction l generalizing Hall with
  | nil =>
    intro _ _ h
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    intro Hall'
    cases Hall' with
    | intro p_hd p_tl =>
      intro i x hg
      cases i with
      | zero =>
        simp [List.get?] at hg
        injection hg with h
        rw [h]
        exact p_hd
      | succ i' =>
        simp [List.get?] at hg
        apply ih
        exact p_tl
        exact hg

-- LLM HELPER
/-- All characters produced by nat_to_bin_list are either '0' or '1'. -/
theorem nat_to_bin_list_all_bits (n : Nat) :
  List.All (fun ch => ch = '0' ∨ ch = '1') (nat_to_bin_list n) := by
  -- Use well-founded induction on n with the same measure as the definition
  apply WellFounded.induction (measure_wf id) n
  intro m ih
  dsimp [nat_to_bin_list]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hm1 : m = 1
  · simp [hm1]
  -- m ≥ 2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let pf := Nat.div_lt_self hmpos
  dsimp
  let d := if m % 2 = 1 then '1' else '0'
  -- rec result for m/2
  have IH := ih (m / 2) pf
  -- From definition nat_to_bin_list m = nat_to_bin_list (m/2) ++ [d]
  -- So All holds by combining All on prefix and the last element
  dsimp [nat_to_bin_list] at *
  -- Build the All for concatenation
  apply List.All.append IH
  -- show predicate for last element d
  dsimp [d]
  by_cases hmod : m % 2 = 1
  · simp [hmod]; exact Or.inr rfl ▸ Or.inl rfl -- produce '1' ∨ '0' (left is '0', right is '1'); adjust:
  -- The above line is awkward; instead directly show d = '0' ∨ d = '1'
  -- Rework:
  show d = '0' ∨ d = '1'
  by
    dsimp [d]
    by_cases h1 : m % 2 = 1
    · simp [h1]; exact Or.inr rfl
    · simp [h1]; exact Or.inl rfl

-- LLM HELPER
theorem nat_to_bin_string_valid (n : Nat) : ValidBitString (nat_to_bin_string n) := by
  dsimp [nat_to_bin_string]
  intro i c hc
  dsimp [String.mk] at hc
  -- reduce to list.get? on nat_to_bin_list n
  have hlist := hc
  -- use All_of_get?_of_All and nat_to_bin_list_all_bits
  have Hall := nat_to_bin_list_all_bits n
  apply All_of_get?_of_All Hall hlist

-- LLM HELPER
/-- Str2Int applied to the binary string produced by nat_to_bin_string returns the original n. -/
theorem Str2Int_nat_to_bin_eq (n : Nat) : Str2Int (nat_to_bin_string n) = n := by
  dsimp [nat_to_bin_string, Str2Int]
  -- Prove by well-founded induction on n
  apply WellFounded.induction (measure_wf id) n
  intro m ih
  dsimp [nat_to_bin_list]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hm1 : m = 1
  · simp [hm1]
  -- m >= 2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let pf := Nat.div_lt_self hmpos
  dsimp
  let dchar := if m % 2 = 1 then '1' else '0'
  have def_list : nat_to_bin_list m = (nat_to_bin_list (m / 2)) ++ [dchar] := by
    -- This follows directly from the definition (unfold the fix once)
    apply WellFounded.fix_eq_lemma (measure_wf id)
    intro k rec
    dsimp [nat_to_bin_list]
    by_cases hk0 : k = 0
    · simp [hk0]
    by_cases hk1 : k = 1
    · simp [hk1]
    -- otherwise, same body; reflexivity suffices
    rfl
    done
  rw [def_list]
  -- compute foldl on l ++ [dchar]
  -- Let L := nat_to_bin_list (m / 2)
  let L := nat_to_bin_list (m / 2)
  have fold_concat :
    (L ++ [dchar]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
    = 2 * (L.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0)
      + (if dchar = '1' then 1 else 0) := by
    -- general property: folding a function which doubles and adds over appended singleton
    -- prove by induction on L
    induction L with
    | nil => simp
    | cons hd tl ih_l =>
      simp [List.foldl]
      have : (tl ++ [dchar]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0))
                    (2 * 0 + (if hd = '1' then 1 else 0))
        = 2 * (tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) (2 * 0 + (if hd = '1' then 1 else 0)))
          + (if dchar = '1' then 1 else 0) := by
          apply ih_l
      simp [this]
  -- apply IH to m/2
  have q := m / 2
  have q_lt : q < m := pf
  have IHq := ih q q_lt
  -- now combine
  calc
    (L ++ [dchar]).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
      = 2 * (L.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) + (if dchar = '1' then 1 else 0) := by
        exact fold_concat
    _ = 2 * q + (if dchar = '1' then 1 else 0) := by
      rw [IHq]
    _ = m := by
      -- show (if dchar = '1' then 1 else 0) = m % 2 and 2 * q + m % 2 = m
      have mod_two : (if dchar = '1' then 1 else 0) = m % 2 := by
        dsimp [dchar]
        -- m % 2 is either 0 or 1
        have Hmod_lt : m % 2 < 2 := Nat.mod_lt m (by decide)
        -- case on m % 2
        have := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) (by decide)) -- dummy to satisfy structure; instead directly do cases
        have hm' : m % 2 = 0 ∨ m % 2 = 1 := by
          have h := (Nat.mod_lt m (by decide))
          cases (m % 2) with
          | zero => exact Or.inl rfl
          | succ n' =>
            -- since m%2 < 2, succ n' must be 1
            have : m % 2 = 1 := by
              cases n'
              case zero => simp
              case succ _ => simp at h; contradiction
            exact Or.inr this
        cases hm' with
        | inl h0 => simp [h0]
        | inr h1 => simp [h1]
      rw [mod_two]
      exact Nat.div_add_mod m 2
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  let r := Exp_int x y % z
  nat_to_bin_string r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  dsimp [ModExp]
  let x := Str2Int sx
  let y := Str2Int sy
  let z := Str2Int sz
  let r := Exp_int x y % z
  have v := nat_to_bin_string_valid r
  have e := Str2Int_nat_to_bin_eq r
  exact ⟨v, e⟩
-- </vc-theorem>
-- <vc-proof>
-- The proof for ModExp_spec is embedded in the theorem statement above.
-- Helpers prove correctness of the binary conversion functions used in ModExp.
-- </vc-proof>

end BignumLean