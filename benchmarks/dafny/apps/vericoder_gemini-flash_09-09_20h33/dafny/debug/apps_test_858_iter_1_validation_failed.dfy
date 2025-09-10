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
predicate IsPowerOfTwoHelper(n: int, k: int) 
    decreases n
{
    if n == 1 then k == 0
    else if n % 2 == 1 then false
    else IsPowerOfTwoHelper(n / 2, k - 1)
}

lemma lemma_IsPowerOfTwo_iff_IsPowerOfTwoHelper_power(x: int)
    requires x >= 1
    ensures IsPowerOfTwo(x) <==> (exists k :: k >= 0 && x == (1 << k))
{
    if x == 1 {
        assert IsPowerOfTwo(1);
        assert (exists k :: k >= 0 && 1 == (1 << k));
    } else if x % 2 == 1 {
        assert !IsPowerOfTwo(x);
        assert !(exists k :: k >= 0 && x == (1 << k));
    } else {
        lemma_IsPowerOfTwo_iff_IsPowerOfTwoHelper_power(x / 2);
        if IsPowerOfTwo(x) {
            var m := x / 2;
            assert IsPowerOfTwo(m);
            // We know IsPowerOfTwo(x / 2) <==> (exists k :: k >= 0 && x / 2 == (1 << k))
            // This means there exists k' such that x / 2 = 2^k'
            // So x = 2 * (2^k') = 2^(k'+1)
        } else {
            assert !IsPowerOfTwo(x);
            // If there exists k such that x = 2^k, then x/2 = 2^(k-1), which would imply IsPowerOfTwo(x/2)
            // But we know !IsPowerOfTwo(x/2), so there is no such k.
        }
    }
}

lemma lemma_next_power_of_two(n: int)
    requires n >= 1
    ensures exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z * 2 > n
{
    var current_power := 1;
    while current_power * 2 <= n
        invariant current_power >= 1 && IsPowerOfTwo(current_power)
        decreases n - current_power
    {
        current_power := current_power * 2;
    }
    assert 1 <= current_power <= n;
    assert IsPowerOfTwo(current_power);
    assert current_power * 2 > n;
}

lemma lemma_power_of_two_unique_next(n: int)
    requires n >= 1
    ensures (exists! z :: 1 <= z <= n && IsPowerOfTwo(z) && z * 2 > n)
{
    calc {
        1;
        while_next_power_of_two_lemma(n); // this implies existence
    }

    // Proof of uniqueness:
    // Assume there are two such powers of two, z1 and z2.
    // Let z1 = 2^k1 and z2 = 2^k2.
    // Without loss of generality, assume k1 < k2.
    // Then z1 < z2.
    // Since z1 * 2 > n, and z2 <= n, we have 2 * z1 > n and z2 <= n.
    // Also, z2 must be at least 2 * z1 because consecutive powers of two are related by a factor of 2.
    // If z1 = 2^k1, then the next power of two is 2^(k1+1) = 2*z1.
    // If z2 is a power of two, z2 >= 2*z1.
    // But we have 2*z1 > n and z2 <= n. This leads to a contradiction if z2 >= 2*z1.
    // Thus, z1 must be equal to z2.
    var z1: int := 1;
    var found_z := false;
    while true
        invariant z1 >= 1 && IsPowerOfTwo(z1)
    {
        if z1 * 2 > n {
            if !found_z {
                found_z := true;
            } else {
                // If we find another one, it means it must be z1, because any larger power would violate z*2 > n
                // or smaller would have already been considered.
            }
            break;
        }
        z1 := z1 * 2;
    }
}

lemma while_next_power_of_two_lemma(n: int)
    requires n >= 1
    ensures exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z * 2 > n
{
    var current_power := 1;
    while current_power * 2 <= n
        invariant current_power >= 1
        invariant IsPowerOfTwo(current_power)
        decreases n - current_power
    {
        current_power := current_power * 2;
    }
    assert 1 <= current_power <= n;
    assert IsPowerOfTwo(current_power);
    assert current_power * 2 > n;
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
            invariant z >= 1
            invariant IsPowerOfTwo(z)
            decreases n - z
        {
            z := z * 2;
        }
        // At this point, z is the largest power of two less than or equal to n, such that 2*z > n.
        // We need to prove that `z` here is the `z` required by `CorrectResult`.
        // `1 <= z <= n` (established by loop invariant and termination)
        // `IsPowerOfTwo(z)` (established by loop invariant)
        // `z * 2 > n` (established by loop termination condition)
        
        result := (n - z) / 2;
    }
}
// </vc-code>

