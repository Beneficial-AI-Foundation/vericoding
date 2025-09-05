This verification task involves implementing a method to determine if a positive integer is a prime number. A prime number is defined as a natural number greater than 1 that has exactly two distinct positive divisors: 1 and itself.

The implementation should efficiently check for primality by testing divisibility up to the square root of the input number, with optimizations for even numbers.

// ======= TASK =======
// Given a positive integer n, determine if it is a prime number. A prime number 
// is a natural number greater than 1 that has exactly two distinct positive divisors: 1 and itself.

// ======= SPEC REQUIREMENTS =======
predicate is_prime_number(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method is_prime(n: int) returns (result: bool)
    ensures result <==> is_prime_number(n)
{
    // Numbers less than 2 are not prime
    if n < 2 {
        return false;
    }

    // 2 is the only even prime number
    if n == 2 {
        return true;
    }

    // All other even numbers are not prime
    if n % 2 == 0 {
        return false;
    }

    // Check odd divisors from 3 up to sqrt(n)
    var i := 3;
    while i * i <= n
        invariant i >= 3 && i % 2 == 1
        invariant forall k :: 2 <= k < i ==> n % k != 0
        invariant n >= 2 && n % 2 != 0
    {
        if n % i == 0 {
            return false;
        }
        i := i + 2;
    }

    // At this point, we know n has no divisors from 2 to i-1
    // and i * i > n, so any divisor >= i would have a corresponding divisor < i
    return true;
}
