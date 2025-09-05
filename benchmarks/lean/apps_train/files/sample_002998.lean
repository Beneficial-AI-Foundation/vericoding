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

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded