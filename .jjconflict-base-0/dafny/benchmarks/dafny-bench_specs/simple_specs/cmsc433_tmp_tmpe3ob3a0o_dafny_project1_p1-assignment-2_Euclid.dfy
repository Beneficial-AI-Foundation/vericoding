// SPEC

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers. If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator). Write requires and
// ensures clauses for the method header Euclid below. Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

method Euclid (m : int, n : int) returns (gcd : int)
  requires m > 1 && n > 1 && m >= n // TODO
  ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0 // TODO
