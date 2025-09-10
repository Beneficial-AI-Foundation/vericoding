predicate ValidTriple(a: int, b: int, c: int, N: int, K: int)
    requires K >= 1
{
    1 <= a <= N && 1 <= b <= N && 1 <= c <= N &&
    (a + b) % K == 0 && (b + c) % K == 0 && (c + a) % K == 0
}

function CountValidTriples(N: int, K: int): int
    requires N >= 1 && K >= 1
{
    if K % 2 == 1 then
        var cnt1 := N / K;
        cnt1 * cnt1 * cnt1
    else
        var cnt1 := N / K;
        var cnt2 := N / K + (if N % K >= K / 2 then 1 else 0);
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
}

predicate ValidInput(N: int, K: int)
{
    N >= 1 && K >= 1
}

function CountDivisibleByK(n: int, K: int): int
    requires K >= 1
{
    if n <= 0 then 0 else n / K
}

function CountWithRemainderHalfK(n: int, K: int): int
    requires K >= 1
{
    if n <= 0 then 0 else n / K + (if n % K >= K / 2 then 1 else 0)
}

// <vc-helpers>
function CountNumbersWithRemainder(N: int, K: int, remainder: int): int
    requires N >= 1 && K >= 1 && 0 <= remainder < K
{
    var count := N / K;
    if N % K >= remainder then count := count + 1;
    return count;
}

function CountNumbersWithRemainderOrInverse(N: int, K: int, r1: int, r2: int): int
    requires N >= 1 && K >= 1
    requires 0 <= r1 < K && 0 <= r2 < K
    requires r1 == (K - r2) % K // r1 and r2 are additive inverses mod K
{
    if r1 == r2 then
        return CountNumbersWithRemainder(N, K, r1);
    else
        return CountNumbersWithRemainder(N, K, r1) + CountNumbersWithRemainder(N, K, r2);
}

predicate SumIsZeroModK(a: int, b: int, K: int)
    requires K >= 1
{
    (a + b) % K == 0
}

predicate ThreeSumIsZeroModK(a: int, b: int, c: int, K: int)
    requires K >= 1
{
    SumIsZeroModK(a, b, K) && SumIsZeroModK(b, c, K) && SumIsZeroModK(c, a, K)
}

lemma Lemma_TripleConsistency(a: int, b: int, c: int, K: int)
    requires K >= 1
    requires (a + b) % K == 0
    requires (b + c) % K == 0
    requires (c + a) % K == 0
    ensures (2 * a) % K == 0
    ensures (2 * b) % K == 0
    ensures (2 * c) % K == 0
{
    // (a+b) + (c+a) - (b+c) = 2a
    calc {
        (a+b) % K;
        0;
    }
    calc {
        (c+a) % K;
        0;
    }
    calc {
        (b+c) % K;
        0;
    }

    var r_ab := (a + b) % K;
    var r_bc := (b + c) % K;
    var r_ca := (c + a) % K;

    assert r_ab == 0;
    assert r_bc == 0;
    assert r_ca == 0;

    // (a+b) + (c+a) = 2a + b + c
    assert ((a+b) + (c+a)) % K == 0; // because both terms are 0 mod K
    assert (2*a + b + c) % K == 0;

    // 2a = (2*a + b + c) - (b + c)
    assert ((2*a + b + c) - (b + c)) % K == 0;
    assert (2*a) % K == 0;

    // Similarly for 2b and 2c
    // (a+b) + (b+c) = a + 2b + c
    assert ((a+b) + (b+c)) % K == 0;
    assert (a + 2*b + c) % K == 0;
    assert ((a + 2*b + c) - (c + a)) % K == 0;
    assert (2*b) % K == 0;

    // (b+c) + (c+a) = b + 2c + a
    assert ((b+c) + (c+a)) % K == 0;
    assert (b + 2*c + a) % K == 0;
    assert ((b + 2*c + a) - (a + b)) % K == 0;
    assert (2*c) % K == 0;
}

lemma Lemma_EvenKRemainderCases(k: int)
    requires k >= 1
    requires k % 2 == 0
    ensures 0 < k / 2 < k
{
    assert k > 0;
    assert k / 2 > 0; // Since k >= 2 and k is even
    assert k / 2 < k; // Since k >= 2
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int) returns (result: int)
    requires ValidInput(N, K)
    ensures result >= 0
    ensures result == CountValidTriples(N, K)
// </vc-spec>
// <vc-code>
{
    if K % 2 == 1 then
        // If K is odd, then if 2r = 0 (mod K), r must be 0 (mod K).
        // Proof: 2r = mK for some integer m.
        // If K is odd, then gcd(2, K) = 1.
        // So by Bezout's identity, there exist integers x, y such that 2x + Ky = 1.
        // Multiplying by r: 2rx + Kym = r.
        // Substitute 2r = mK: (mK)x + Kym = r.
        // K(mx + ym) = r.
        // This implies r is a multiple of K, so r % K == 0.
        // Therefore, (a, b, c) must all have remainder 0 mod K.
        // So we count multiples of K for a, b, c.
        var count_mult_k := N / K;
        result := count_mult_k * count_mult_k * count_mult_k;
    else // K is even
        // If K is even, then 2r = 0 (mod K) implies r can be 0 or K/2 (mod K).
        //
        // From Lemma_TripleConsistency, we know that 2a % K == 0, 2b % K == 0, 2c % K == 0.
        // This means (a % K) can be 0 or K/2.
        // (b % K) can be 0 or K/2.
        // (c % K) can be 0 or K/2.
        //
        // Let a_rem = a % K, b_rem = b % K, c_rem = c % K.
        //
        // Case 1: a_rem = 0, b_rem = 0, c_rem = 0.
        // Count: (N/K) * (N/K) * (N/K)
        //
        // Case 2: a_rem = 0, b_rem = K/2, c_rem = K/2.
        // Condition: (a+b)%K=0 => 0+K/2 = K/2 != 0 (mod K). This case is impossible.
        // Oh, wait.
        //
        // Let's analyze the remainders (r_a, r_b, r_c):
        // r_a + r_b == 0 (mod K)
        // r_b + r_c == 0 (mod K)
        // r_c + r_a == 0 (mod K)
        //
        // From Lemma_TripleConsistency, 2*r_a % K == 0, 2*r_b % K == 0, 2*r_c % K == 0.
        // So each remainder r_i must be either 0 or K/2.
        //
        // Let r_0 = 0 and r_half_K = K/2.
        //
        // If (r_a, r_b, r_c) are all 0: (0, 0, 0)
        //   0+0=0, 0+0=0, 0+0=0. This works.
        //
        // If (r_a, r_b, r_c) are all K/2: (K/2, K/2, K/2)
        //   K/2 + K/2 = K = 0 (mod K). This works.
        //
        // If (r_a, r_b, r_c) include both 0 and K/2:
        // Assume r_a = 0.
        // Then r_a + r_b = r_b = 0 (mod K). So r_b must be 0.
        // If r_b = 0, then r_b + r_c = r_c = 0 (mod K). So r_c must be 0.
        // This means if any remainder is 0, all must be 0.
        //
        // So for K even, the only valid remainder triples (r_a, r_b, r_c) are:
        // (0, 0, 0)
        // (K/2, K/2, K/2)
        //
        // Therefore, we need to count:
        // 1. Numbers up to N that are multiples of K (remainder 0).
        // 2. Numbers up to N that have remainder K/2 when divided by K.

        var count_rem_0 := N / K; // Count numbers of the form mK
        var count_rem_half_K := N / K; // Count numbers of the form mK + K/2
        if N % K >= K / 2 then
            count_rem_half_K := count_rem_half_K + 1; // If N has remainder >= K/2, then mK + K/2 is also counted
        
        // Total valid triples = (count of all three having remainder 0) + (count of all three having remainder K/2)
        result := count_rem_0 * count_rem_0 * count_rem_0 +
                  count_rem_half_K * count_rem_half_K * count_rem_half_K;
    
    // Dafny can verify the equivalence between this logic and the `CountValidTriples` function.
    // The `CountValidTriples` function effectively captures this logic for K odd and K even.
    // For K odd, K/2 is not a relevant remainder. `N % K >= K/2` will be true for roughly half the values,
    // making `CountWithRemainderHalfK` and `CountDivisibleByK` effectively the same as `N/K`
    // which results in the (N/K)^3 formula.
    // For K even, `N/K` is `cnt1`, and `N/K + (N % K >= K/2 ? 1 : 0)` is `cnt2`.
    // The proof that `ValidTriple` implies `a%K`, `b%K`, `c%K` are all 0 or all K/2 is key.
    
    assert result == CountValidTriples(N, K);
}
// </vc-code>

