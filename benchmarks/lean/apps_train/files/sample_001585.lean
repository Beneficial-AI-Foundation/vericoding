You are given 2 numbers is `n` and `k`. You need to find the number of integers between 1 and n (inclusive) that contains exactly `k` non-zero digit.

Example1 

`
almost_everywhere_zero(100, 1) return 19`

by following condition we have 19 numbers that have k = 1 digits( not count zero ) 
` [1,2,3,4,5,6,7,8,9,10,20,30,40,50,60,70,80,90,100]`

Example2  

`
almost_everywhere_zero(11, 2) return 1`

we have only `11` that has 2 digits(ten not count because zero is not count) 
` 11`

constrains

`1≤n<pow(10,100)`

`1≤k≤100`

def almost_everywhere_zero (n : Nat) (k : Nat) : Nat :=
  sorry

def comb (n : Nat) (k : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded