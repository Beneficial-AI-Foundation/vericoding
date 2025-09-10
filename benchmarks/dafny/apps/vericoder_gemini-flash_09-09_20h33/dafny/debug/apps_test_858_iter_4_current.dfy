predicate IsPowerOfTwo(n: int) 
    decreases n
{
    if n <= 0 then false
    else if n == 1 then true
    else if n % 2 == 1 then false
    else IsPowerOfTwo(n / 2)
}

predicate ValidInput(n: int) {
    n >= 1
}

predicate CorrectResult(n: int, result: int) {
    if n % 2 == 1 then 
        result == (n - 1) / 2
    else 
        exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n && result == (n - z) / 2
}

// <vc-helpers>
predicate IsPowerOfTwo_lemma(z: int)
    requires z >= 1
{
    (z as bv64 & (z - 1) as bv64) == 0bv64
}

lemma IsPowerOfTwo_equivalent_lemma(n: int)
    requires n >= 1
    ensures IsPowerOfTwo(n) == IsPowerOfTwo_lemma(n)
{
    if n == 1 {
        assert IsPowerOfTwo(1);
        assert (1 as bv64 & (1 - 1) as bv64) == 0bv64;
    } else if n % 2 == 1 {
        // IsPowerOfTwo(n) is false
        // IsPowerOfTwo_lemma(n): n is odd, so n-1 is even. n & (n-1) will have the least significant bit set to 1 if n is odd and > 1.
        // For example, if n = 3 (011), n-1 = 2 (010). n & (n-1) = 010 (2) != 0.
        // If n = 5 (101), n-1 = 4 (100). n & (n-1) = 100 (4) != 0.
        if n > 1 {
            assert !IsPowerOfTwo_lemma(n);
        }
    } else { // n is even
        if n / 2 >= 1 {
            IsPowerOfTwo_equivalent_lemma(n / 2);
            assert IsPowerOfTwo(n) == IsPowerOfTwo(n / 2);
            // This assertion is not correct as a general property and depends on the base and context.
            // assert (n as bv64 & (n - 1) as bv64) == 0bv64 <==> ((n / 2) as bv64 & (n / 2 - 1) as bv64) == 0bv64 && n % 2 == 0; // Property of powers of 2 (except 0)
            // Correct approach: if n is a power of 2, and n is even, then n/2 is also a power of 2.
            // If n is a power of 2, then n & (n-1) == 0.
            // If n/2 is a power of 2, then (n/2) & (n/2 - 1) == 0.
            // These are equivalent for positive even n.
            assert IsPowerOfTwo_lemma(n) <==> IsPowerOfTwo_lemma(n / 2);
        }
    }
}

lemma find_largest_power_of_two_lemma(n: int) returns (z: int)
    requires n >= 1
    ensures 1 <= z <= n && IsPowerOfTwo(z) && z * 2 > n
{
    var current_z := 1;
    while current_z * 2 <= n
        invariant current_z >= 1 && IsPowerOfTwo(current_z)
        decreases n - current_z
    {
        current_z := current_z * 2;
    }
    return current_z;
}

lemma largest_power_of_two_property(n: int, z: int)
    requires n >= 1
    requires z >= 1 && IsPowerOfTwo(z) && z <= n && z * 2 > n
    ensures forall k :: 1 <= k <= n && IsPowerOfTwo(k) ==> k <= z
{
    forall k | 1 <= k <= n && IsPowerOfTwo(k)
        ensures k <= z
    {
        if k > z {
            // k must be a larger power of two
            // and k <= n
            // z * 2 > n
            // Since k is a power of 2 and k > z, it must be k >= 2 * z
            // But 2 * z > n, so k > n, which contradicts k <= n.
            if IsPowerOfTwo(k) && IsPowerOfTwo(z) {
                // If k > z and both are powers of two, then k must be at least 2*z
                assert k >= 2 * z;
                assert k > n; // because 2*z > n
                // this implies k can't be <= n, so the assumption k > z must be false
                // Thus k <= z must hold.
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures CorrectResult(n, result)
// </vc-spec>
// <vc-code>
{
    if n % 2 == 1 {
        result := (n - 1) / 2;
    } else {
        var z := 1;
        while z * 2 <= n
            invariant z >= 1 && IsPowerOfTwo(z)
            decreases n - z
        {
            z := z * 2;
        }

        // At this point, z is the largest power of two less than or equal to n.
        // It satisfies 1 <= z <= n and IsPowerOfTwo(z) and z * 2 > n.
        // We need to prove that this z is the one required by the postcondition.
        // The postcondition says "exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n"
        // The one we found satisfies this.
        // The 'exists' quantifier doesn't require this z to be unique, but our 'z' is indeed the largest.
        largest_power_of_two_property(n, z);
        result := (n - z) / 2;
    }
}
// </vc-code>

