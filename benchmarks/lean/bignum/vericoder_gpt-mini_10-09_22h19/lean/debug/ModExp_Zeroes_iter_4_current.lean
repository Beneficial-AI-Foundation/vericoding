namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
theorem List_foldl_append_single {α β : Type} (f : β → α → β) (l : List α) (z : β) (a : α) :
  (l ++ [a]).foldl f z = f (l.foldl f z) a := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl]; show (tl ++ [a]).foldl f (f z hd) = f ((tl.foldl f (f z hd))) a
    apply ih

-- LLM HELPER
def bits_of : Nat -> List Char
  | 0     => ['0']
  | n + 1 =>
    let m := n + 1
    let q := m / 2
    (bits_of q) ++ [if m % 2 = 1 then '1' else '0']
termination_by bits_of n => n

-- LLM HELPER
def Int2Str (n : Nat) : String := String.mk (bits_of n)

-- LLM HELPER
theorem bits_of_spec (n : Nat) :
  (bits_of n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  apply Nat.strong_induction_on n
  intro k IH
  cases k
  case zero => simp [bits_of]
  case succ k' =>
    let m := k' + 1
    let q := m / 2
    have qlt : q < m := Nat.div_lt_self (by decide : 2 > 1)
    have hq := IH q qlt
    -- compute foldl on the appended list
    simp [bits_of]
    have : ((bits_of q ++ [if m % 2 = 1 then '1' else '0']).
            foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) =
           (bits_of q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 +
           (if m % 2 = 1 then 1 else 0) := by
      simp [List.foldl_append]
      simp [List_foldl_append_single]
    simp [this, hq]
    -- use division algorithm
    have : m = 2 * q + m % 2 := by
      calc
        m = (m / 2) * 2 + m % 2 := Nat.div_mod_eq m 2
        _ = 2 * q + m % 2 := by rfl
    rw [this]
    rfl

-- LLM HELPER
theorem Int2Str_Str2Int (n : Nat) :
  Str2Int (Int2Str n) = n := by
  -- by definition Int2Str n = String.mk (bits_of n)
  show (String.mk (bits_of n)).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n
  simp [Str2Int, Int2Str]
  -- String.mk stores the list as .data, so reduce to bits_of_spec
  have : (String.mk (bits_of n)).data = bits_of n := rfl
  rw [this]
  exact bits_of_spec n

-- LLM HELPER
theorem bits_of_chars_are_bits (n : Nat) :
  ∀ c ∈ bits_of n, c = '0' ∨ c = '1' := by
  apply Nat.strong_induction_on n
  intro k IH
  cases k
  case zero =>
    simp [bits_of]; intro c h; simp at h; rcases h with rfl; simp
  case succ k' =>
    let m := k' + 1
    let q := m
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
theorem List_foldl_append_single {α β : Type} (f : β → α → β) (l : List α) (z : β) (a : α) :
  (l ++ [a]).foldl f z = f (l.foldl f z) a := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl]; show (tl ++ [a]).foldl f (f z hd) = f ((tl.foldl f (f z hd))) a
    apply ih

-- LLM HELPER
def bits_of : Nat -> List Char
  | 0     => ['0']
  | n + 1 =>
    let m := n + 1
    let q := m / 2
    (bits_of q) ++ [if m % 2 = 1 then '1' else '0']
termination_by bits_of n => n

-- LLM HELPER
def Int2Str (n : Nat) : String := String.mk (bits_of n)

-- LLM HELPER
theorem bits_of_spec (n : Nat) :
  (bits_of n).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n := by
  apply Nat.strong_induction_on n
  intro k IH
  cases k
  case zero => simp [bits_of]
  case succ k' =>
    let m := k' + 1
    let q := m / 2
    have qlt : q < m := Nat.div_lt_self (by decide : 2 > 1)
    have hq := IH q qlt
    -- compute foldl on the appended list
    simp [bits_of]
    have : ((bits_of q ++ [if m % 2 = 1 then '1' else '0']).
            foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0) =
           (bits_of q).foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 * 2 +
           (if m % 2 = 1 then 1 else 0) := by
      simp [List.foldl_append]
      simp [List_foldl_append_single]
    simp [this, hq]
    -- use division algorithm
    have : m = 2 * q + m % 2 := by
      calc
        m = (m / 2) * 2 + m % 2 := Nat.div_mod_eq m 2
        _ = 2 * q + m % 2 := by rfl
    rw [this]
    rfl

-- LLM HELPER
theorem Int2Str_Str2Int (n : Nat) :
  Str2Int (Int2Str n) = n := by
  -- by definition Int2Str n = String.mk (bits_of n)
  show (String.mk (bits_of n)).data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = n
  simp [Str2Int, Int2Str]
  -- String.mk stores the list as .data, so reduce to bits_of_spec
  have : (String.mk (bits_of n)).data = bits_of n := rfl
  rw [this]
  exact bits_of_spec n

-- LLM HELPER
theorem bits_of_chars_are_bits (n : Nat) :
  ∀ c ∈ bits_of n, c = '0' ∨ c = '1' := by
  apply Nat.strong_induction_on n
  intro k IH
  cases k
  case zero =>
    simp [bits_of]; intro c h; simp at h; rcases h with rfl; simp
  case succ k' =>
    let m := k' + 1
    let q := m
-- </vc-code>

end BignumLean