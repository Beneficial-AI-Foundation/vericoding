# Task
 You are given a string consisting of `"D", "P" and "C"`. A positive integer N is called DPC of this string if it satisfies the following properties: 

 ```
 For each i = 1, 2, ... , size of the string:

 If i-th character is "D", then N can be divided by i
 If i-th character is "P", then N and i should be relatively prime
 If i-th character is "C", then N should neither be divided by i 
                           nor be relatively prime with i```

Your task is to find the smallest DPC of a given string, or return `-1` if there is no such. The result is guaranteed to be `<= 10^9`.

# Example
 For `s = "DDPDD"`, the result should be `20`.

 `"DDPDD"` means `N` should `divided by 1,2,4,5`, and `N,3` should be relatively prime. The smallest N should be `20`.

# Input/Output

 - `[input]` string `s`

  The given string

 - `[output]` an integer

  The smallest DPC of `s` or `-1` if it doesn't exist.

def gcd (a b : Nat) : Nat :=
  sorry

def hasDPCProperties (n : Nat) (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded