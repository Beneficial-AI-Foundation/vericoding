predicate ValidInput(n: int)
{
    n >= 1
}

predicate DivisibleByBoth(result: int, n: int)
    requires n >= 1
{
    result % 2 == 0 && result % n == 0
}

predicate IsSmallest(result: int, n: int)
    requires n >= 1
{
    forall k: int :: 1 <= k < result ==> !(k % 2 == 0 && k % n == 0)
}

function LCM(a: int, b: int): int
    requires a >= 1 && b >= 1
{
    if a % b == 0 then a
    else if b % a == 0 then b
    else a * b
}

// <vc-helpers>
lemma LCMProperties(n: int)
    requires n >= 1
    ensures n % 2 == 0 ==> LCM(2, n) == n
    ensures n % 2 != 0 ==> LCM(2, n) == n * 2
{
    if n % 2 == 0 {
        // n is even, so n is divisible by 2
        assert n % 2 == 0;
        assert LCM(2, n) == n;
    } else {
        // n is odd, so gcd(2, n) = 1, thus LCM(2, n) = 2 * n
        assert n % 2 != 0;
        // We don't need to assert 2 % n != 0 for all n
        // When n = 1, we have 2 % 1 == 0, but LCM(2, 1) = 2 = 1 * 2
        if n == 1 {
            assert LCM(2, n) == 2;
            assert 2 == n * 2;
        } else {
            assert n > 1;
            assert 2 % n != 0;
            assert LCM(2, n) == 2 * n;
        }
    }
}

lemma SmallestDivisibleByBoth(n: int, result: int)
    requires n >= 1
    requires result >= 1
    requires result % 2 == 0 && result % n == 0
    requires (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2)
    ensures IsSmallest(result, n)
{
    forall k: int | 1 <= k < result
        ensures !(k % 2 == 0 && k % n == 0)
    {
        if n % 2 == 0 {
            // result == n
            assert result == n;
            if k % 2 == 0 && k % n == 0 {
                assert k % n == 0;
                // If k is divisible by n and k >= 1, then k >= n
                assert k >= n || k <= 0;
                assert k >= 1;  // from precondition
                assert k >= n;
                assert k < result;
                assert k < n;
                assert false;
            }
        } else {
            // result == n * 2
            assert result == n * 2;
            if k % 2 == 0 && k % n == 0 {
                // k is even and divisible by n
                // k must be a multiple of n: k = m * n for some m >= 1
                // Since k is even and n is odd, m must be even
                // So m >= 2, which means k >= 2 * n
                var m := k / n;
                assert k == m * n;
                assert k % 2 == 0;
                assert n % 2 != 0;
                // Since k is even and n is odd, m must be even
                assert m % 2 == 0;
                assert m >= 2 || m <= 0;
                assert k >= 1;
                assert m >= 1;
                assert m >= 2;
                assert k >= 2 * n;
                assert k < result;
                assert k < n * 2;
                assert false;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures DivisibleByBoth(result, n)
    ensures IsSmallest(result, n)
    ensures (n % 2 == 0 ==> result == n) && (n % 2 != 0 ==> result == n * 2)
// </vc-spec>
// <vc-code>
{
    if n % 2 == 0 {
        result := n;
    } else {
        result := n * 2;
    }
    
    LCMProperties(n);
    SmallestDivisibleByBoth(n, result);
}
// </vc-code>

