Implement the [Polybius square cipher](http://en.wikipedia.org/wiki/Polybius_square).

Replace every letter with a two digit number. The first digit is the row number, and the second digit is the column number of following square. Letters `'I'` and `'J'` are both 24 in this cipher:

table#polybius-square {width: 100px;}
table#polybius-square td {background-color: #2f2f2f;}
table#polybius-square th {background-color: #3f3f3f;}

12345
1ABCDE
2FGHI/JK
3LMNOP
4QRSTU
5VWXYZ

Input will be valid (only spaces and uppercase letters from A to Z), so no need to validate them.

## Examples

```python
polybius('A')  # "11"
polybius('IJ') # "2424"
polybius('CODEWARS') # "1334141552114243"
polybius('POLYBIUS SQUARE CIPHER') # "3534315412244543 434145114215 132435231542"
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded