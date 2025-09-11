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
-- (no additional helpers required)
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
if decide (Str2Int s1 < Str2Int s2) then (-1 : Int)
  else if decide (Str2Int s1 = Str2Int s2) then 0
  else 1
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
dsimp [Compare]
constructor
· intro h
  have hdec := decide_eq_true (Str2Int s1 < Str2Int s2) h
  simp [hdec]
· constructor
  · intro heq
    have not_lt : ¬ Str2Int s1 < Str2Int s2 := by
      intro hl
      rw [heq.symm] at hl
      exact Nat.lt_irrefl _ hl
    have hdec1 := decide_eq_false (Str2Int s1 < Str2Int s2) not_lt
    have hdec2 := decide_eq_true (Str2Int s1 = Str2Int s2) heq
    simp [hdec1, hdec2]
  · intro hgt
    have not_lt : ¬ Str2Int s1 < Str2Int s2 := by
      intro hl
      exact Nat.lt_asymm hl hgt
    have not_eq : ¬ Str2Int s1 = Str2Int s2 := by
      intro heq; subst heq; exact Nat.lt_irrefl _ hgt
    have hdec1 := decide_eq_false (Str2Int s1 < Str2Int s2) not_lt
    have hdec2 := decide_eq_false (Str2Int s1 = Str2Int s2) not_eq
    simp [hdec1, hdec2]
-- </vc-proof>

end BignumLean