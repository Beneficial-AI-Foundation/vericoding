A common problem in number theory is to find x given a such that:

a * x = 1 mod [n] 

Then x is called the inverse of a modulo n. 

Your goal is to code a function inverseMod wich take a and n as parameters and return x.

You may be interested by these pages:

http://en.wikipedia.org/wiki/Modular_multiplicative_inverse

http://en.wikipedia.org/wiki/Extended_Euclidean_algorithm

a and n should be co-prime to have a solution, if it is not the case, you should return None (Python), nil (Ruby) or null (Javascript). 

a and n will be positive integers. The problem can easily be generalised to negative integer with some sign changes so we won't deal with them.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible