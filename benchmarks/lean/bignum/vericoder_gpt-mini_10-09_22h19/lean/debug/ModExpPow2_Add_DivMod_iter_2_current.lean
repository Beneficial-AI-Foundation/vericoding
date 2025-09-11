namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
def bin_build : Nat → String × Nat
  | 0 => ("0", 0)
  | k+1 =>
    let k' := k+1
    let q := k' / 2
    let b := k' % 2
    let (s, v) := bin_build q
    (s ++ (if b = 1 then "1" else "0"), 2 * v + b)

-- LLM HELPER
def nat_to_bin (k : Nat) : String := (bin_build k).1

-- LLM HELPER
theorem bin_build_correct (k : Nat) :
  let (s, v) := bin_build k in ValidBitString s ∧ v = k ∧ Str2Int s = k := by
  induction k with
  | zero =>
    dsimp [bin_build]
    simp [ValidBitString, Str2Int]
    -- bin_build 0 = ("0", 0)
    constructor
    · -- ValidBitString "0"
      intro i c
      simp [String.get?] at *
      -- only index 0 yields '0'
      cases i
      · simp_all
      · simp_all
    constructor
    · rfl
    · dsimp [Str2Int]
      -- Str2Int "0" = 0 by computation
      have : ("0").data = [ '0' ] := by
        -- string literal "0" has data defined as single char list
        rfl
      dsimp [Str2Int]
      -- compute with foldl
      change ("0").data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0
      -- fold on single char '0' gives 0
      simp [*]
  | succ k ih =>
    let k' := k + 1
    let q := k' / 2
    let b := k' % 2
    dsimp [bin_build]
    let ⟨s, v⟩ := bin_build q
    have IH := ih q
    -- unpack IH for q
    have IHspec := IH
    dsimp at IHspec
    -- IH gives ValidBitString s ∧ v = q ∧ Str2Int s = q
    have vs : ValidBitString s := (IHspec.1)
    have v_eq_q : v = q := (IHspec.2.1)
    have s_val_q : Str2Int s = q := (IHspec.2.2)
    -- Now show for built string s ++ bit
    constructor
    · -- ValidBitString (s ++ bit)
      intro i c hi
      -- s ++ bit has either characters from s or the final bit
      have : (s ++ (if b = 1 then "1" else "0")).get? i = some c := hi
      -- We reason by cases on whether i indexes into s or the last char
      -- Use general facts about String.get? for append by cases on i
      by
        -- do cases on i
        cases i
        · -- i = 0
          -- either head of s or head of appended char when s is empty; handle uniformly
          match s.get? 0 with
          | some ch =>
            simp at this
            exact Or.inr (Or.inr rfl) -- placeholder to keep structure; we will simplify below
          | none =>
            simp at this
            -- then c must be the appended single char
            have hb : (if b = 1 then "1" else "0") = (if b = 1 then "1" else "0") := rfl
            simp [hb] at this
            -- the only possible char is '1' or '0'
            cases b
            · simp at this; injection this with h; subst h; exact Or.inl rfl
            · simp at this; injection this with h; subst h; exact Or.inl rfl
        · -- i > 0: reduce to s.get? (i-1)
          simp at this
          -- fallback: use the ValidBitString property of s
          -- We can produce a trivial proof by using vs
          apply vs
          simp_all
    constructor
    · -- v component equals k'
      dsimp [bin_build]
      -- v = 2 * v + b where v on RHS is from recursive call; use v_eq_q
      have : (bin_build q).2 = q := by
        dsimp at IHspec; exact v_eq_q
      dsimp [bin_build] at *
      -- compute numeric value: 2*q + b = k'
      calc
        2 * (bin_build q).2 + b = 2 * q + b := by rw [this]
        _ = k' := by
          -- q = k' / 2 and b = k' % 2, so 2*q + b = k'
          have h := Nat.div_add_mod k' 2
          -- Nat.div_add_mod: 2 * (k' / 2) + k' % 2 = k'
          rw [Nat.mul_comm] at h
          exact h.symm
    · -- Str2Int (s ++ bit) = k'
      dsimp [bin_build]
      -- compute Str2Int using foldl and List.foldl_append
      dsimp [Str2Int]
      -- rewrite (s ++ bit).data as s.data ++ [ch], then use List.foldl_append
      let ch := if b = 1 then '1' else '0'
      have hdata : (if b = 1 then "1"
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def bin_build : Nat → String × Nat
  | 0 => ("0", 0)
  | k+1 =>
    let k' := k+1
    let q := k' / 2
    let b := k' % 2
    let (s, v) := bin_build q
    (s ++ (if b = 1 then "1" else "0"), 2 * v + b)

-- LLM HELPER
def nat_to_bin (k : Nat) : String := (bin_build k).1

-- LLM HELPER
theorem bin_build_correct (k : Nat) :
  let (s, v) := bin_build k in ValidBitString s ∧ v = k ∧ Str2Int s = k := by
  induction k with
  | zero =>
    dsimp [bin_build]
    simp [ValidBitString, Str2Int]
    -- bin_build 0 = ("0", 0)
    constructor
    · -- ValidBitString "0"
      intro i c
      simp [String.get?] at *
      -- only index 0 yields '0'
      cases i
      · simp_all
      · simp_all
    constructor
    · rfl
    · dsimp [Str2Int]
      -- Str2Int "0" = 0 by computation
      have : ("0").data = [ '0' ] := by
        -- string literal "0" has data defined as single char list
        rfl
      dsimp [Str2Int]
      -- compute with foldl
      change ("0").data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0
      -- fold on single char '0' gives 0
      simp [*]
  | succ k ih =>
    let k' := k + 1
    let q := k' / 2
    let b := k' % 2
    dsimp [bin_build]
    let ⟨s, v⟩ := bin_build q
    have IH := ih q
    -- unpack IH for q
    have IHspec := IH
    dsimp at IHspec
    -- IH gives ValidBitString s ∧ v = q ∧ Str2Int s = q
    have vs : ValidBitString s := (IHspec.1)
    have v_eq_q : v = q := (IHspec.2.1)
    have s_val_q : Str2Int s = q := (IHspec.2.2)
    -- Now show for built string s ++ bit
    constructor
    · -- ValidBitString (s ++ bit)
      intro i c hi
      -- s ++ bit has either characters from s or the final bit
      have : (s ++ (if b = 1 then "1" else "0")).get? i = some c := hi
      -- We reason by cases on whether i indexes into s or the last char
      -- Use general facts about String.get? for append by cases on i
      by
        -- do cases on i
        cases i
        · -- i = 0
          -- either head of s or head of appended char when s is empty; handle uniformly
          match s.get? 0 with
          | some ch =>
            simp at this
            exact Or.inr (Or.inr rfl) -- placeholder to keep structure; we will simplify below
          | none =>
            simp at this
            -- then c must be the appended single char
            have hb : (if b = 1 then "1" else "0") = (if b = 1 then "1" else "0") := rfl
            simp [hb] at this
            -- the only possible char is '1' or '0'
            cases b
            · simp at this; injection this with h; subst h; exact Or.inl rfl
            · simp at this; injection this with h; subst h; exact Or.inl rfl
        · -- i > 0: reduce to s.get? (i-1)
          simp at this
          -- fallback: use the ValidBitString property of s
          -- We can produce a trivial proof by using vs
          apply vs
          simp_all
    constructor
    · -- v component equals k'
      dsimp [bin_build]
      -- v = 2 * v + b where v on RHS is from recursive call; use v_eq_q
      have : (bin_build q).2 = q := by
        dsimp at IHspec; exact v_eq_q
      dsimp [bin_build] at *
      -- compute numeric value: 2*q + b = k'
      calc
        2 * (bin_build q).2 + b = 2 * q + b := by rw [this]
        _ = k' := by
          -- q = k' / 2 and b = k' % 2, so 2*q + b = k'
          have h := Nat.div_add_mod k' 2
          -- Nat.div_add_mod: 2 * (k' / 2) + k' % 2 = k'
          rw [Nat.mul_comm] at h
          exact h.symm
    · -- Str2Int (s ++ bit) = k'
      dsimp [bin_build]
      -- compute Str2Int using foldl and List.foldl_append
      dsimp [Str2Int]
      -- rewrite (s ++ bit).data as s.data ++ [ch], then use List.foldl_append
      let ch := if b = 1 then '1' else '0'
      have hdata : (if b = 1 then "1"
-- </vc-code>

end BignumLean