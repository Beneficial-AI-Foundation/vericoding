-- <vc-preamble>
@[reducible]
def allVowels_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower
-- </vc-helpers>

-- <vc-definitions>
def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))

theorem allVowels_spec_satisfied (s: String) (h_precond : allVowels_precond (s)) :
    allVowels_postcond (s) (allVowels (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>