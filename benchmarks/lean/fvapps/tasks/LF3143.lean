-- <vc-preamble>
def stringAppend (s1 s2: String) : String := String.append s1 s2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (pattern: String) (target: String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_strings_match
  (s: String)
  (h: s.data.all (fun c => c ≠ '*')) :
  solve s s = true :=
sorry

theorem wildcard_match
  (p s m: String)
  (h1: p.data.all (fun c => c ≠ '*'))
  (h2: s.data.all (fun c => c ≠ '*'))
  (h3: m.data.all (fun c => c ≠ '*')) :
  solve (stringAppend (stringAppend p "*") s) (stringAppend (stringAppend p m) s) = true :=
sorry

theorem different_strings_no_match
  (s1 s2: String)
  (h1: s1.data.all (fun c => c ≠ '*'))
  (h2: s2.data.all (fun c => c ≠ '*'))
  (h3: s1 ≠ s2) :
  solve s1 s2 = false :=
sorry

theorem multiple_wildcards_invalid
  (s1 s2: String)
  (h1: s1.data.all (fun c => c ≠ '*'))
  (h2: s2.data.all (fun c => c ≠ '*')) :
  solve (stringAppend (stringAppend (stringAppend s1 "*") s2) "*") "anything" = false :=
sorry

theorem length_requirement
  (p s m: String)
  (h1: p.data.all (fun c => c ≠ '*'))
  (h2: s.data.all (fun c => c ≠ '*')) :
  (stringAppend (stringAppend p m) s).length ≥ (stringAppend (stringAppend p "*") s).length - 1 :=
sorry
-- </vc-theorems>