A *[Hamming number][1]* is a positive integer of the form 2*i*3*j*5*k*, for some non-negative integers *i*, *j*, and *k*.

Write a function that computes the *n*th smallest Hamming number. 

Specifically:

  - The first smallest Hamming number is 1 = 2^(0)3^(0)5^(0)
  - The second smallest Hamming number is 2 = 2^(1)3^(0)5^(0)
  - The third smallest Hamming number is 3 = 2^(0)3^(1)5^(0)
  - The fourth smallest Hamming number is 4 = 2^(2)3^(0)5^(0)
  - The fifth smallest Hamming number is 5 = 2^(0)3^(0)5^(1)

The 20 smallest Hamming numbers are given in example test fixture.

Your code should be able to compute all of the smallest 5,000 (Clojure: 2000, NASM: 13282) Hamming numbers without timing out.

[1]:https://en.wikipedia.org/wiki/Regular_number

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
