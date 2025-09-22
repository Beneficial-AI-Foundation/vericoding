-- <vc-preamble>
def Photo := String

def Year := Nat

def ImgNum := Nat

instance : Inhabited Photo := ⟨""⟩

instance : LT Year := ⟨Nat.lt⟩

instance : LT ImgNum := ⟨Nat.lt⟩

instance : HAdd ImgNum Nat ImgNum := ⟨Nat.add⟩

instance : LT (Year × ImgNum) := ⟨λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)⟩
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_photos (photos : List Photo) : List Photo :=
  sorry

def parse_year (photo : Photo) : Year :=
  sorry

def parse_imgnum (photo : Photo) : ImgNum :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_photos_length (photos : List Photo) :
  photos ≠ [] →
  photos.length > 0 →
  let result := sort_photos photos
  result.length = min photos.length 5 + 1 := by
  sorry

theorem sort_photos_contains_originals (photos : List Photo) :
  photos ≠ [] →
  let result := sort_photos photos
  ∀ i, i < result.length - 1 → result[i]! ∈ photos := by
  sorry

theorem sort_photos_sorted (photos : List Photo) :
  photos ≠ [] →
  let result := sort_photos photos
  ∀ i j, i < j → j < result.length - 1 →
    (parse_year result[i]!, parse_imgnum result[i]!) <
    (parse_year result[j]!, parse_imgnum result[j]!) := by
  sorry

theorem sort_photos_last_increments (photos : List Photo) :
  photos ≠ [] →
  let result := sort_photos photos
  parse_year result[result.length-1]! = parse_year result[result.length-2]! ∧
  parse_imgnum result[result.length-1]! = parse_imgnum result[result.length-2]! + 1 := by
  sorry

theorem sort_photos_format_valid (photos : List Photo) :
  photos ≠ [] →
  let result := sort_photos photos
  ∀ p ∈ result, ∃ y n : Nat,
    y ≥ 1000 ∧ y ≤ 9999 ∧
    n > 0 ∧
    parse_year p = y ∧
    parse_imgnum p = n := by
  sorry
-- </vc-theorems>