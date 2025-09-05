Everyone Knows AdFly and their Sister Sites.

If we see the Page Source of an ad.fly site we can see this perticular line:
Believe it or not This is actually the Encoded url which you would skip to.

The Algorithm is as Follows:
```
1) The ysmm value is broken like this

ysmm   = 0 1 2 3 4 5 6 7 8 9  = "0123456789"
code1  = 0   2   4   6   8    = "02468"
code2  =   9   7   5   3   1  = "97531"

2) code1+code2 is base64 Decoded

3) The result will be of this form :
https://adf.ly/go.php?u=

4)  has to be further decoded and the result is to be returned
```

Your Task:

```
Make a function to Encode text to ysmm value.

and a function to Decode ysmm value.
```

Note: Take random values for The first 2 int values.
I personally hate trivial error checking like giving integer input in place of string. 

```
Input For Decoder & Encoder: Strings
Return "Invalid" for invalid Strings
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded