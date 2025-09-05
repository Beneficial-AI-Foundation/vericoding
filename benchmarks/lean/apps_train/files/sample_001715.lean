A pixmap shall be turned from black to white, turning all pixels to white in the process.  But for optical reasons this shall *not* happen linearly, starting at the top and continuing line by line to the bottom:

```python
for y in range(height):
  for x in range(width):
     setBit(x, y)
```

Instead it shall be done by a systematic dithering routine which selects the coordinates on which pixels are to be set in a precise pattern so that the geometrical distance between two consecutive pixels is large and a specific optical effect results.

The following diagrams show the order of the coordinates the algorithm shall produce:

2×2:
```
1 3
4 2
```
4×4:
```
 1  9  3 11
13  5 15  7
 4 12  2 10
16  8 14  6
```
8×8:
```
 1  33   9  41   3  35  11  43 
49  17  57  25  51  19  59  27 
13  45   5  37  15  47   7  39 
61  29  53  21  63  31  55  23 
 4  36  12  44   2  34  10  42 
52  20  60  28  50  18  58  26 
16  48   8  40  14  46   6  38 
64  32  56  24  62  30  54  22 
```
The pattern continues like that for each square pixmap with a width and height of a power of two (16, 32, 64, …).

But the width and the height of the pixmap can be arbitrary positive numbers.  If the pixmap's width and/or height are not a power of two, the coordinates the algorithm  would produce outside of the pixmap are skipped:

3×3:
```
1 6 3
8 5 9
4 7 2   
```
6×5:
```
 1 16  6 21  3 18
25 10 28 13 26 11
 8 23  5 20  9 24
29 14 27 12 30 15
 4 19  7 22  2 17
```
Write an algorithm which produces the coordinates of the dithering for a given width and height.

To pass the Python test cases, write a *generator* ```dithering()``` which yields coordinate tuples:
```python
g = dithering(6, 5)
for i in range(7):
  print g.next()
```
Will print:
```
(0, 0)
(4, 4)
(4, 0)
(0, 4)
(2, 2)
(2, 0)
(2, 4)
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
