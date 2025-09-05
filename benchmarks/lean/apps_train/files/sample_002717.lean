The number 81 has a special property, a certain power of the sum of its digits is equal to 81 (nine squared). Eighty one (81), is the first number in having this property (not considering numbers of one digit). 
The next one, is 512.
Let's see both cases with the details

8 + 1 = 9 and 9^(2) = 81

512 = 5 + 1 + 2 = 8 and 8^(3) = 512

We need to make a function, ```power_sumDigTerm()```, that receives a number ```n``` and may output the ```n-th term``` of this sequence of numbers.
The cases we presented above means that

power_sumDigTerm(1) == 81

power_sumDigTerm(2) == 512

Happy coding!

def toDigits (n : Nat) : List Nat :=
  if n < 10 then [n]
  else (n % 10) :: toDigits (n / 10)

def sum_list : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + sum_list t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
