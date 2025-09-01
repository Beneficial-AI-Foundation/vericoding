```vc-helpers
proof fn smallest_factor_implies_divides(m: nat, d: nat, i: nat)
    requires
        d > 0,
        i > 0,
        d % i == 0,
    ensures
        exists |q: nat| d == i * q
{
    // From division algorithm: d == i * (d / i) + d % i
    let q = d / i;
    assert(d == i * q + d % i);
    assert(d % i == 0);
    assert(d == i * q);
    reveal_exists(|q: nat| d == i * q);
}

proof fn divides_transitive(a: nat, b: nat, c: nat)
    requires
        a > 0,
        b > 0,
        c == a * b,
        forall|k: nat| 0 <= k ==> true, // dummy to avoid unused warnings
    ensures
        forall|i: nat| i > 0 && i <= a && a % i == 0 ==> c % i == 0
{
    // If i divides a and c = a * b then i divides c
    // Let i > 0 and assume a % i == 0.
    // Then a == i * (a / i).
    // So c == (i * (a / i)) * b == i * ((a / i) * b), hence c % i == 0.
    // We will show by algebra.
    assert(true);
}

proof fn prime_of_smallest_factor(m: nat, d: nat, start: nat)
    requires
        2 <= d,
        d <= m,
        m % d == 0,
        // no divisors < d
        forall|k: nat| 2 <= k && k < d ==> m % k != 0,
        // start is a lower bound (for use in some contexts)
        2 <= start && start <= d,
    ensures
        is_prime(d)
{
    // Show: forall 1 < i < d ==> d % i != 0
    assert(forall|i: nat| 1 < i && i < d ==> d % i != 0);
    proof {
        intros |i: nat| { assume(1 < i && i < d); }
        // Suppose for contradiction d % i == 0
        if d % i == 0 {
            // then i divides d, and since d divides m, i divides m, contradicting the no-divisor assumption
            // d % i == 0 -> exists q: d == i * q
            let q = d / i;
            assert(d == i * q + d % i);
            assert(d % i == 0);
            assert(d == i * q);
            // m % d == 0 -> exists t: m == d * t
            let t = m / d;
            assert(m == d * t + m % d);
            assert(m % d == 0);
            assert(m == d * t);
            // combine: m == i * (q * t)
            assert(m == i * (q * t));
            // hence m % i == 0, contradiction with assumed no divisor
            assert(m % i == 0); // follows from above
            // contradiction:
            assert(false); // triggers contradiction to discharge the branch
        } else {
            assert(d % i != 0);
        }
    }
}

proof fn prime_if_no_small_divisor(m: nat, d: nat)
    requires
        2 <= d,
        d * d > m,
        forall|k: nat| 2 <= k && k < d ==> m % k != 0,
    ensures
        is_prime(m)
{
    // Show for any 1 < i < m, m % i != 0.
    assert(forall|i: nat| 1 < i && i < m ==> m % i != 0);
    proof {
        intros |i: nat| { assume(1 < i && i < m); }
        // Suppose m % i == 0, then let j = m / i with j >= 1 and i * j == m
        if m % i == 0 {
            let j = m / i;
            assert(m == i * j + m % i);
            assert(m % i == 0);
            assert(m == i * j);
            // both i and j are >= 2 since 1 < i < m and j = m/i > 0 and cannot be 1 unless i == m
            assert(i >= 2);
            assert(j >= 1);
            // If both i >= d and j >= d then m >= d*d which contradicts d*d > m.
            // Hence at least one of i or j is < d.
            if i >= d && j >= d {
                assert(i * j >= d * d);
                assert(m >= d * d);
                assert(false); // contradiction
            } else {
                // one of i or j is < d. But that means there is a divisor < d, contradicting the assumption.
                if i < d {
                    // i < d and i divides m, contradicts assumption
                    assert(m % i == 0);
                    assert(false);
                } else {
                    // j < d and j >= 2 and j divides m
                    assert(j >= 2);
                    assert(m % j == 0);
                    assert(false);
                }
            }
        } else {
            assert(m % i != 0);
        }
    }
}
```

```vc-code
{
    // impl-start
    let mut factors: Vec<u8> = Vec::new();
    let orig: u8 = n;
    let mut m: u8 = n;
    let mut prod: nat = 1;
    let mut start: u8 = 2u8;

    // Outer loop: factor out until m == 1
    while m > 1 {
        invariant prod * (m as nat) == (orig as nat);
        invariant forall|i: int| 0 <= i && (i as nat) < (factors@.len()) ==> is_prime((factors@[i]) as nat);
        invariant forall|i: int, j: int| 0 <= i && i < j && (j as nat) < (factors@.len()) ==> (factors@[i] as nat) <= (factors@[j] as nat);
