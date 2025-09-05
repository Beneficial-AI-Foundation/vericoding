Consider the following well known rules:

- A number is divisible by 3 if the sum of its digits is divisible by 3. Let's call '3' a "1-sum" prime
- For 37, we take numbers in groups of threes from the right and check if the sum of these groups is divisible by 37. 
  Example: 37 * 123456787 = 4567901119 => 4 + 567 + 901 + 119 = 1591 = 37 * 43. Let's call this a "3-sum" prime because we use groups of 3.
- For 41, we take numbers in groups of fives from the right and check if the sum of these groups is divisible by 41. This is a "5-sum" prime.
- Other examples: 239 is a "7-sum" prime (groups of 7), while 199 is a "99-sum" prime (groups of 99).

Let's look at another type of prime:
- For 11, we need to add all digits by alternating their signs from the right. 
  Example: 11 * 123456 = 1358016 => 6-1+0-8+5-3+1 = 0, which is divible by 11. Let's call this a "1-altsum" prime
- For 7, we need to group the digits into threes from the right and add all groups by alternating their signs.
  Example: 7 * 1234567891234 = 8641975238638 => 638 - 238 + 975 - 641 + 8 = 742/7 = 106. 
- 7 is a "3-altsum" prime because we use groups of threes. 47 is a "23-altsum" (groups of 23), while 73 is a "4-altsum" prime (groups of 4).

You will be given a prime number `p` and your task is to find the smallest positive integer `n` such that `p’s` divisibility testing is `n-sum` or `n-altsum`.

For example:
```
solve(3) = "1-sum"
solve(7) = "3-altsum"
```
Primes will not exceed `50,000,000`. More examples in test cases. 

You can get some insight from [Fermat's little theorem](https://en.wikipedia.org/wiki/Fermat%27s_little_theorem). 

Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded