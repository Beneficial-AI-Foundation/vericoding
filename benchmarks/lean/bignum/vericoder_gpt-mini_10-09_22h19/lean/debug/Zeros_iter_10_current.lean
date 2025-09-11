namespace BignumLean

def AllZero (s : String) : Prop :=
  s.length = 0 ∨ ∀ i, s.get? i = some '0'

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

-- <vc-helpers>
-- LLM HELPER
theorem String_append_data (s t : String) : (s ++ t).data = s.data ++ t.data := rfl

theorem String_length_data (s : String) : s.length = s.data.length := rfl

theorem String_length_append (s t : String) : (s ++ t).length = s.length + t.length := by
  calc
    (s ++ t).length = (s ++ t).data.length := (String_length_data _).symm
    _ = (s.data ++ t.data).length := by rw [String_append_data]
    _ = s.data.length + t.data.length := by rw [List.length_append]
    _ = s.length + t.length := by rw [String_length_data, String_length_data]

theorem String_push_data (s : String) (c : Char) : (s.push c).data = s.data ++ [c] := rfl

theorem String_length_push (s : String) (c : Char) : (s.push c).length = s.length + 1 := by
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  calc
    (s.push c).length = (s.push c).data.length := (String_length_data _).symm
    _ = (s.data ++ [c]).length := by rw [this]
    _ = s.data.length + [c].length := by rw [List.length_append]
    _ = s.data.length + 1 := by simp
    _ = s.length + 1 := by rw [String_length_data]

theorem List_get?_append_last {α} (l : List α) (x : α) : (l ++ [x]).get? l.length = some x := by
  induction l with
  | nil => simp [List.get?]
  | cons hd tl ih =>
    -- index l.length = tl.length + 1 for hd::tl
    simp [List.get?]
    exact ih

theorem List_get?_of_lt_append_last {α} (l : List α) (x : α) {i : Nat} (h : i < l.length) : (l ++ [x]).get? i = l.get? i := by
  induction l generalizing i with
  | nil => simp [List.get?] at h; contradiction
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.get?]
    | succ i' =>
      simp [List.get?]
      apply ih
      exact h

theorem List_get?_lt_length {α} {l : List α} {j : Nat} {a : α} (h : l.get? j = some a) : j < l.length := by
  induction l generalizing j with
  | nil =>
    simp [List.get?] at h
    contradiction
  | cons hd tl ih =>
    cases j with
    | zero => simp [List.get?] at h; exact Nat.zero_lt_succ _
    | succ j' =>
      simp [List.get?] at h
      apply Nat.succ_lt_succ
      apply ih
      exact h

-- Convert between String.get? on a String.Pos and access into .data via String.Pos.toNat
-- LLM HELPER
theorem String_get?_to_data (s : String) (p : String.Pos) : s.get? p = s.data.get? (String.Pos.toNat p) := by
  cases s; rfl

-- LLM HELPER
theorem String_get?_mk_nat (s : String) (i : Nat) : s.get? (String.Pos.mk i) = s.data.get? i := by
  -- String.Pos.mk i's toNat is definitionally i
  have : String.Pos.toNat (String.Pos.mk i) = i := by rfl
  calc
    s.get? (String.Pos.mk i) = s.data.get? (String.Pos.toNat (String.Pos.mk i)) := by rw [String_get?_to_data]
    _ = s.data.get? i := by rw [this]

-- LLM HELPER
theorem String_get?_data_to_pos (s : String) (i : Nat) : s.data.get? i = s.get? (String.Pos.mk i) := by
  rw [String_get?_mk_nat]

theorem String_get?_lt_length (t : String) {p : String.Pos} {ch : Char} (h : t.get? p = some ch) : String.Pos.toNat p < t.length := by
  have : t.data.get? (String.Pos.toNat p) = some ch := by
    rw [String_get?_to_data] at h
    exact h
  have := List_get?_lt_length this
  rwa [String_length_data] at this

theorem Str2Int_push (s : String) (c : Char) :
  Str2Int (s.push c) = 2 * Str2Int s + (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  have : (s.push c).data = s.data ++ [c] := String_push_data s c
  rw [this]
  have h := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data [c]
  rw [h]
  simp
-- </vc-helpers>

-- <vc-spec>
def Zeros (n : Nat) : String :=
-- </vc-spec>
-- <vc-code>
def Zeros (n : Nat) : String :=
  match n with
  | 0 => ""
  | n+1 => (Zeros n).push '0'
-- </vc-code>

-- <vc-theorem>
theorem Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ (∀ i, i < s.length → s.get? (String.Pos.mk i) = some '0') :=
-- </vc-theorem>
-- <vc-proof>
open Nat
by
  induction n with
  | zero =>
    dsimp [Zeros]
    let s := Zeros 0
    constructor
    . -- length = 0
      dsimp [s]; simp [String_length_data]
    . -- ValidBitString ∧ Str2Int = 0 ∧ all-zero
      constructor
      . -- ValidBitString: empty string has no gets
        intros p c h
        rw [String_get?_to_data] at h
        simp [List.get?] at h
        contradiction
      . constructor
        . -- Str2Int "" = 0
          dsimp [Str2Int]; simp
        . -- no indices less than 0
          intros i h; exact False.elim (Nat.not_lt_zero i h)
  | succ n ih =>
    -- ih : let s := Zeros n; ... properties for s
    have ih' := ih
    let s := Zeros n
    let t := Zeros (n+1)
    -- break ih' into components
    have : let s' := Zeros n in s'.length = n ∧ ValidBitString s' ∧ Str2Int s' = 0 ∧ (∀ i, i < s'.length → s'.get? (String.Pos.mk i) = some '0') := ih'
    have ⟨hlen, hvalid, hstr, hall⟩ := this
    -- length
    constructor
    . calc
        t.length = (s.push '0').length := rfl
        _ = s.length + 1 := String_length_push s '0'
        _ = n + 1 := by rw [hlen]
    -- ValidBitString ∧ Str2Int = 0 ∧ all-zero
    . constructor
      -- ValidBitString
      . intros p c hp
        -- move to data-level index k
        have getdata : t.data.get? (String.Pos.toNat p) = some c := by
          rw [String_get?_to_data] at hp
          exact hp
        -- k < t.length
        have klt : String.Pos.toNat p < t.length := by
          apply String_get?_lt_length t hp
        -- t.length = s.length + 1
        have tlen : t.length = s.length + 1 := by
          calc
            t.length = (s.push '0').length := rfl
            _ = s.length + 1 := String_length_push s '0'
        -- compare k with s.length
        have kle : String.Pos.toNat p ≤ s.length := Nat.le_of_lt_succ (by rwa [tlen] at klt)
        cases (Nat.eq_or_lt_of_le kle) with
        | inl heq =>
          -- k = s.length, last element must be '0'
          have : t.data = s.data ++ ['0'] := by
            rw [String_push_data s '0']
          have kdef : String.Pos.toNat p = s.data.length := by
            rw [heq, String_length_data]
          have last := List_get?_append_last s.data '0'
          -- rewrite to get the character
          have tmp : (s.data ++ ['0']).get? s.data.length = some '0' := last
          rw [← kdef] at tmp
          -- convert t.data.get? k to that
          have getk_eq : t.data.get? (String.Pos.toNat p) = (s.data ++ ['0']).get? s.data.length := by
            rw [kdef, ← this]
          rw [getk_eq] at getdata
          -- now getdata = some c and tmp = some '0' so c = '0'
          injection getdata with hc
          rw [hc]; left; rfl
        | inr hlt =>
          -- k < s.length: then t.data.get? k = s.data.get? k and by IH s.get? mk k = some '0'
          have sd := List_get?_of_lt_append_last s.data '0' (by
            -- need k < s.data.length
            have : String.Pos.toNat p < s.length := by
              have tlen' : t.length = s.length + 1 := tlen
              exact Nat.lt_of_lt_succ (by rwa [tlen'] at klt)
            rwa [String_length_data] at this
          )
          -- relate t.get? (pos) with s.get? via data
          have eq1 : t.data.get? (String.Pos.toNat p) = s.data.get? (String.Pos.toNat p) := sd
          rw [eq1] at getdata
          -- now get s.data.get? k = some c, convert to s.get? (mk k)
          have get_s_pos : s.get? (String.Pos.mk (String.Pos.toNat p)) = s.data.get? (String.Pos.toNat p) := by
            rw [String_get?_mk_nat]
          rw [← get_s_pos] at getdata
          -- use IH's all property: need k < s.length
          have klt_s : String.Pos.toNat p < s.length := by
            have tlen' : t.length = s.length + 1 := tlen
            exact Nat.lt_of_lt_succ (by rwa [tlen'] at klt)
          have all_s := hall (String.Pos.toNat p) klt_s
          -- all_s : s.get? (mk k) = some '0'
          rw [all_s] at getdata
          injection getdata with hc
          rw [hc]; left; rfl
      -- Str2Int = 0 and all-zero
      . constructor
        . -- Str2Int t = 2 * Str2Int s + 0 = 0
          calc
            Str2Int t = 2 * Str2Int s + (if '0' = '1' then 1 else 0) := by rw [Str2Int_push s '0']
            _ = 2 * 0 + 0 := by rw [hstr]; simp
            _ = 0 := by simp
        . -- all indices are '0'
          intro i h
          -- t.get? (mk i) = t.data.get? i
          have getdata : t.data.get? i = t.get? (String.Pos.mk i) := by
            rw [String_get?_mk_nat t i]; rfl
          -- t.data = s.data ++ ['0']
          have tdata : t.data = s.data ++ ['0'] := by rw [String_push_data s '0']
          -- if i = s.data.length then last element; else use IH
          have : i ≤ s.data.length := by
            have tlen : t.length = s.length + 1 := by
              calc
                t.length = (s.push '0').length := rfl
                _ = s.length + 1 := String_length_push s '0'
            have : i < t.length := h
            exact Nat.le_of_lt_succ (by rwa [tlen] at this)
          cases (Nat.eq_or_lt_of_le this) with
          | inl heq =>
            -- i = s.data.length
            have i_eq_len : i = s.data.length := heq
            have last := List_get?_append_last s.data '0'
            have tmp : (s.data ++ ['0']).get? s.data.length = some '0' := last
            rw [tdata] at tmp
            rw [i_eq_len] at tmp
            -- rewrite getdata
            have g := by
              rw [String_get?_mk_nat t i]
            -- now conclude
            rw [String_get?_mk_nat t i]
            rw [tdata]
            rw [i_eq_len]
            exact tmp
          | inr hlt =>
            -- i < s.data.length; use List_get?_of_lt_append_last and IH
            have sd := List_get?_of_lt_append_last s.data '0' (by
              have : i < s.length := by
                have tlen : t.length = s.length + 1 := by
                  calc
                    t.length = (s.push '0').length := rfl
                    _ = s.length + 1 := String_length_push s '0'
                exact Nat.lt_of_lt_succ (by rwa [tlen] at h)
              rwa [String_length_data] at this
            )
            -- sd : (s.data ++ ['0']).get? i = s.data.get? i
            have : t.data.get? i = s.data.get? i := by
              rw [tdata]; exact sd
            rw [String_get?_mk_nat t i] at this
            -- convert s.data.get? i to s.get? (mk i)
            have sconv := (String_get?_data_to_pos s i)
            rw [sconv] at this
            -- apply IH all
            have all_s := hall i (by
              have tlen : t.length = s.length + 1 := by
                calc
                  t.length = (s.push '0').length := rfl
                  _ = s.length + 1 := String_length_push s '0'
              exact Nat.lt_of_lt_succ (by rwa [tlen] at h)
            )
            rw [all_s] at this
            exact all_s
-- </vc-proof>

end BignumLean