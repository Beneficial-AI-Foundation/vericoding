// Question 1 (5 points)
//
// Fill in a requires clause that enables Dafny to verify
// method PlusOne

pub fn PlusOne(x: int) -> (y: int)
    requires(x >= 0)
    ensures(|y: int| y > 0)
{
}

// Question 2 (5 points)
//
// Fill in requires clause(s) that enable(s) Dafny to verify the array bounds
// in method Swap (which swaps elements i and j in array a).

pub fn Swap(a: &mut [int], i: int, j: int)
    requires(0 <= i < a.len() && 0 <= j < a.len())
{
}

// Question 3 (5 points)
//
// Give ensures clause(s) asserting that d is the result, and r the
// remainder, of dividing m by n.  Your clauses cannot use "/" or "%" (which are
// the Dafny division and mod operators, respectively). By definition, the
// remainder must be non-negative.

pub fn IntDiv(m: int, n: int) -> (d: int, r: int)
    requires(n > 0)
    ensures(|d: int, r: int| m == n * d + r && 0 <= r < n)
{
}

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

pub fn ArraySum(a: &[int], b: &[int]) -> (c: Vec<int>)
    requires(a.len() == b.len())
    ensures(|c: Vec<int>| c.len() == a.len() && 
        forall|i: int| 0 <= i < c.len() ==> c[i] == a[i] + b[i])
{
}

// Question 5 (10 points)

// Euclid's algorithm is used to compute the greatest common divisor of two
// positive integers.  If m and n are two such integers, then gcd(m,n) is the
// largest positve integer that evenly divides both m and n, where j evenly divides i
// if and only if i % j == 0 (% is the Dafny mod operator).  Write requires and
// ensures clauses for the method header Euclid below.  Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

pub fn Euclid(m: int, n: int) -> (gcd: int)
    requires(m > 1 && n > 1 && m >= n)
    ensures(|gcd: int| gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0)
{
}

// Question 6 (10 points)
//
// Give invariant(s) that enable(s) Dafny to verify the following program, which
// returns true if and only if array a is sorted.

pub fn IsSorted(a: &[int]) -> (isSorted: bool)
    ensures(|isSorted: bool| isSorted <==> forall|j: int| 1 <= j < a.len() ==> a[j-1] <= a[j])
{
}

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

pub fn IsPrime(m: int) -> (isPrime: bool)
    requires(m > 0)
    ensures(|isPrime: bool| isPrime <==> (m > 1 && forall|j: int| 2 <= j < m ==> m % j != 0))
{
}

// Question 8 (20 points)
//
// Implement, and have Dafny verify, the method Reverse below, which returns a new array
// aRev consisting of the elements of a, but in reverse order.  To create a new 
// array of ints use the Dafny command "new int[...]", where "..." is the number
// of elements in the array.

pub fn Reverse(a: &[int]) -> (aRev: Vec<int>)
    ensures(|aRev: Vec<int>| aRev.len() == a.len())
    ensures(|aRev: Vec<int>| forall|i: int| 0 <= i < a.len() ==> a[i] == aRev[aRev.len()-i-1])
{
}

// Question 9 (20 points)
//
// Implement and verify method NoDups, which returns true if and only if there
// are no duplicate elements in array a.  Note that the requires clause allows
// you to assume that a is sorted, and that this precondition is necessary for
// the ensures clause to imply a lack of duplicates.

pub fn NoDups(a: &[int]) -> (noDups: bool)
    requires(forall|j: int| 0 < j < a.len() ==> a[j-1] <= a[j])
    ensures(|noDups: bool| noDups <==> forall|j: int| 1 <= j < a.len() ==> a[j-1] != a[j])
{
}