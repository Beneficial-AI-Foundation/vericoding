-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_min (n : Nat) (seq : String) : Int × Int :=
sorry

def maximum : List Int → Int :=
sorry

def minimum : List Int → Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_min_permutation_invariant {nums1 nums2 : List Int} (n : Nat)
  (seq1 seq2 : String)
  (h1 : n = nums1.length)
  (h2 : n = nums2.length)
  (h3 : seq1 = String.intercalate " " (List.map toString nums1))
  (h4 : seq2 = String.intercalate " " (List.map toString nums2))
  (h5 : nums2.isPerm nums1) :
  find_max_min n seq1 = find_max_min n seq2 :=
sorry

theorem find_max_min_single_element (n : Nat) (x : Int) (seq : String)
  (h1 : n = 1)
  (h2 : seq = toString x) :
  find_max_min n seq = (x, x) :=
sorry
-- </vc-theorems>