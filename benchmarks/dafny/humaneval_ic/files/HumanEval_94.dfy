This verification task involves implementing a method that finds the largest prime number in a given list of integers and returns the sum of its digits. If no prime number exists in the list, the method should return 0. The implementation requires helper functions for prime checking and digit sum calculation.

// ======= TASK =======
// Given a list of integers, find the largest prime number in the list and return the sum of its digits.
// If no prime exists in the list, return 0.

// ======= SPEC REQUIREMENTS =======
function is_prime_pure(n: int): bool
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}

function sum_of_digits_pure(n: int): int
    requires n >= 0
{
    if n < 10 then n else (n % 10) + sum_of_digits_pure(n / 10)
}

// ======= HELPERS =======
method is_prime(n: int) returns (prime: bool)
    ensures prime == is_prime_pure(n)
{
    if n < 2 {
        return false;
    }
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    var i := 3;
    while i * i <= n
        invariant 3 <= i
        invariant i % 2 == 1
        invariant forall k :: 2 <= k < i ==> n % k != 0
        invariant n >= 2
    {
        if n % i == 0 {
            return false;
        }
        i := i + 2;
    }

    assert forall k :: 2 <= k < n ==> n % k != 0 by {
        forall k | 2 <= k < n 
        ensures n % k != 0
        {
            if k < i {
                // Already covered by loop invariant
            } else {
                assert k >= i;
                assert i * i > n;
                if n % k == 0 {
                    var m := n / k;
                    assert n == k * m;
                    assert m >= 1;
                    if m == 1 {
                        assert n == k;
                        assert k < n;
                        assert false;
                    } else {
                        assert m >= 2;
                        assert k * m == n;
                        assert k >= i;
                        assert i * i > n;
                        assert k * m < k * k;
                        assert m < k;
                        assert m < i;
                        assert n % m == 0;
                        assert false;
                    }
                }
            }
        }
    }
    return true;
}

function sum_of_digits(n: int): int
    requires n >= 0
    ensures sum_of_digits(n) == sum_of_digits_pure(n)
    ensures sum_of_digits(n) >= 0
{
    if n < 10 then n
    else (n % 10) + sum_of_digits(n / 10)
}

// ======= MAIN METHOD =======
method skjkasdkd(lst: seq<int>) returns (result: int)
    ensures result >= 0
    ensures (forall x :: x in lst ==> !is_prime_pure(x)) ==> result == 0
    ensures (exists x :: x in lst && is_prime_pure(x)) ==> 
        (exists largest :: largest in lst && is_prime_pure(largest) && 
         (forall y :: y in lst && is_prime_pure(y) ==> y <= largest) &&
         result == sum_of_digits_pure(largest))
{
    var primes: seq<int> := [];
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall j :: 0 <= j < |primes| ==> primes[j] in lst && is_prime_pure(primes[j])
        invariant forall x :: x in lst[..i] && is_prime_pure(x) ==> x in primes
    {
        var prime_check := is_prime(lst[i]);
        if prime_check {
            primes := primes + [lst[i]];
        }
        i := i + 1;
    }

    if |primes| == 0 {
        assert forall x :: x in lst ==> !is_prime_pure(x);
        return 0;
    }

    var largest_prime := primes[0];
    i := 1;
    while i < |primes|
        invariant 1 <= i <= |primes|
        invariant largest_prime in primes
        invariant forall j :: 0 <= j < i ==> primes[j] <= largest_prime
    {
        if primes[i] > largest_prime {
            largest_prime := primes[i];
        }
        i := i + 1;
    }

    assert largest_prime in lst && is_prime_pure(largest_prime);
    assert forall y :: y in lst && is_prime_pure(y) ==> y <= largest_prime;
    assert largest_prime >= 2;
    return sum_of_digits(largest_prime);
}
