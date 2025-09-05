In this Kata we focus on finding a sum S(n) which is the total number of divisors taken for all natural numbers less or equal to n. More formally, we investigate the sum of n components denoted by d(1) + d(2) + ... + d(n) in which for any i starting from 1 up to n the value of d(i) tells us how many distinct numbers divide i without a remainder. 

Your solution should work for possibly large values of n without a timeout.
Assume n to be greater than zero and not greater than 999 999 999 999 999.
Brute force approaches will not be feasible options in such cases. It is fairly simple to conclude that for every n>1 there holds a recurrence S(n) = S(n-1) + d(n) with initial case S(1) = 1.

For example:
S(1) = 1
S(2) = 3
S(3) = 5
S(4) = 8
S(5) = 10

But is the fact useful anyway? If you find it is rather not, maybe this will help: 

Try to convince yourself that for any natural k, the number S(k) is the same as the number of pairs (m,n) that solve the inequality mn <= k in natural numbers.
Once it becomes clear, we can think of a partition of all the solutions into classes just by saying that a pair (m,n) belongs to the class indexed by n.
The question now arises if it is possible to count solutions of n-th class. If f(n) stands for the number of solutions that belong to n-th class, it means that S(k) = f(1) + f(2) + f(3) + ...

The reasoning presented above leads us to some kind of a formula for S(k), however not necessarily the most efficient one. Can you imagine that all the solutions to inequality mn <= k can be split using sqrt(k) as pivotal item?

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
