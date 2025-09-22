-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def same_encryption (s1 s2 : String) : Bool := sorry

theorem same_encryption_reflexive 
  (s : String) 
  (h : s.length > 0) : 
  same_encryption s s = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_encryption_symmetric
  (s1 s2 : String)
  (h1 : s1.length > 0)
  (h2 : s2.length > 0) :
  same_encryption s1 s2 = same_encryption s2 s1 := sorry

theorem same_encryption_transitive
  (s1 s2 s3 : String)
  (h1 : s1.length > 0)
  (h2 : s2.length > 0)
  (h3 : s3.length > 0)
  (h4 : same_encryption s1 s2 = true)
  (h5 : same_encryption s2 s3 = true) :
  same_encryption s1 s3 = true := sorry

theorem same_encryption_first_last_only
  (s1 s2 : String)
  (h1 : s1.length > 1)
  (h2 : s2.length > 1) :
  let test_s1 := String.mk [s1.front] ++ String.mk (List.replicate (s1.length - 2) 'x') ++ String.mk [s1.back]
  let test_s2 := String.mk [s2.front] ++ String.mk (List.replicate (s2.length - 2) 'y') ++ String.mk [s2.back]
  same_encryption s1 s2 = same_encryption test_s1 test_s2 := sorry

theorem same_encryption_empty_raises 
  (h : same_encryption "" "" = true ∨ same_encryption "" "" = false) :
  False := sorry
-- </vc-theorems>