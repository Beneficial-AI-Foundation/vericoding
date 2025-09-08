/-
An array of size N x M represents pixels of an image.
Each cell of this array contains an array of size 3 with the pixel's color information: `[R,G,B]`

Convert the color image, into an *average* greyscale image. 

The `[R,G,B]` array contains integers between 0 and 255 for each color. 

To transform a color pixel into a greyscale pixel, average the values of that pixel:
```
p = [R,G,B] => [(R+G+B)/3, (R+G+B)/3, (R+G+B)/3]
```

**Note:** the values for the pixel must be integers, therefore you should round floats to the nearest integer.

## Example

Here's an example of a 2x2 image: 

Here's the expected image after transformation:

You are always welcome to check out some of my other katas:

Very Easy (Kyu 8)
Add Numbers
Easy (Kyu 7-6)
Convert Color image to greyscale
Array Transformations
Basic Compression
Find Primes in Range
No Ifs No Buts
Medium (Kyu 5-4)
Identify Frames In An Image
Photoshop Like - Magic Wand
Scientific Notation
Vending Machine - FSA
Find Matching Parenthesis
Hard (Kyu 3-2)
Ascii Art Generator
-/

-- <vc-helpers>
-- </vc-helpers>

def color_2_grey (colors: List (List (List (List Nat)))) : List (List (List (List Nat))) := sorry

-- Shape preservation theorems

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

-- Apps difficulty: introductory
-- Assurance level: guarded