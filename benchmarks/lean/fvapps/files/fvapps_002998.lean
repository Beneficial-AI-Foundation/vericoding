-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def color_2_grey (colors: List (List (List (List Nat)))) : List (List (List (List Nat))) := sorry

-- Shape preservation theorems
-- </vc-definitions>

-- <vc-theorems>
theorem color_2_grey_preserves_outer_length {colors: List (List (List (List Nat)))} :
  List.length (color_2_grey colors) = List.length colors := sorry

theorem color_2_grey_preserves_image_length {colors: List (List (List (List Nat)))} (img_idx: Nat) 
  (h: img_idx < List.length colors) :
  List.length (List.get! (color_2_grey colors) img_idx) = 
  List.length (List.get! colors img_idx) := sorry

theorem color_2_grey_preserves_row_length {colors: List (List (List (List Nat)))} 
  (img_idx row_idx: Nat)
  (h1: img_idx < List.length colors)
  (h2: row_idx < List.length (List.get! colors img_idx)) :
  List.length (List.get! (List.get! (color_2_grey colors) img_idx) row_idx) = 
  List.length (List.get! (List.get! colors img_idx) row_idx) := sorry

-- Grey value properties

theorem color_2_grey_output_pixels_equal {colors: List (List (List (List Nat)))}
  (img_idx row_idx pixel_idx: Nat)
  (h1: img_idx < List.length colors)
  (h2: row_idx < List.length (List.get! colors img_idx))
  (h3: pixel_idx < List.length (List.get! (List.get! colors img_idx) row_idx)) :
  let grey_pixel := List.get! (List.get! (List.get! (color_2_grey colors) img_idx) row_idx) pixel_idx
  List.length grey_pixel = 3 ∧ 
  List.get! grey_pixel 0 = List.get! grey_pixel 1 ∧
  List.get! grey_pixel 1 = List.get! grey_pixel 2 := sorry

theorem color_2_grey_value_between_minmax {colors: List (List (List (List Nat)))}
  (img_idx row_idx pixel_idx: Nat)
  (h1: img_idx < List.length colors)
  (h2: row_idx < List.length (List.get! colors img_idx))
  (h3: pixel_idx < List.length (List.get! (List.get! colors img_idx) row_idx)) :
  let original := List.get! (List.get! (List.get! colors img_idx) row_idx) pixel_idx
  let grey_pixel := List.get! (List.get! (List.get! (color_2_grey colors) img_idx) row_idx) pixel_idx
  let min := List.get! original 0 
  let max := List.get! original 0
  (min ≤ List.get! grey_pixel 0) ∧ (List.get! grey_pixel 0 ≤ max) := sorry

theorem color_2_grey_is_average {colors: List (List (List (List Nat)))}
  (img_idx row_idx pixel_idx: Nat)
  (h1: img_idx < List.length colors)
  (h2: row_idx < List.length (List.get! colors img_idx))
  (h3: pixel_idx < List.length (List.get! (List.get! colors img_idx) row_idx)) :
  let original := List.get! (List.get! (List.get! colors img_idx) row_idx) pixel_idx
  let grey_pixel := List.get! (List.get! (List.get! (color_2_grey colors) img_idx) row_idx) pixel_idx
  let total := List.get! original 0 + List.get! original 1 + List.get! original 2
  List.get! grey_pixel 0 = (total + 2) / 3 := sorry
-- </vc-theorems>