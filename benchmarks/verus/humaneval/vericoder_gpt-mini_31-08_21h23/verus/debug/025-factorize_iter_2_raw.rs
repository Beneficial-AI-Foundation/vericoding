```vc-helpers
proof fn divides_transitive(k: nat, i: nat, m: nat)
    requires
        i % k == 0,
        m % i == 0,
    ensures
        m % k == 0,
{
    // i = k * (i / k)
    let q_i_k = i / k;
    assert(i == k * q_i_k);
    // m = i * (m / i)
    let q_m_i = m / i;
    assert(m == i * q_m_i);
    // combine: m = k * (q_i_k * q_m_i)
    assert(m == k * (q_i_k * q_m_i));
    // hence divisible
    assert(m % k == 0);
}

proof fn minimal_divisor_is_prime(m: nat, i: nat)
    requires
        2 <= i <= m,
        m % i == 0,
        forall|k: nat| 2 <= k && k < i ==> m % k != 0,
    ensures
        is_prime(i),
{
    // We need to show: forall d. 1 < d < i ==> i % d != 0
    assert(forall|d: nat| 1 < d && d < i ==> i % d != 0) by {
        fix d;
        assume H1: 1 < d && d < i;
        // Suppose d divides i; then by transitivity d divides m, contradicting minimality.
        assume Hdiv: i % d == 0;
        divides_transitive(d, i, m);
        assert(m % d == 0);
        // This contradicts the hypothesis that no k in [2, i) divides m.
        assert(false);
    };
    // Now by definition this is exactly is_prime(i)
}
```

```vc-code
{
    // impl-start
    let mut m: nat = n as nat;
    let orig: nat = m;
    let mut res: Vec<u8> = Vec::new();
    let mut f: u8 = 2;
    let mut prod: nat = 1;

    // If n == 1, no factors, return empty vector
    if m == 1 {
        return res;
    }

    while (f as nat) <= m {
        invariant 0 <= m && m <= orig;
        invariant prod * m == orig;
        invariant forall|k: nat| 2 <= k && k < (f as nat) ==> m % k != 0;
        invariant res@.fold_right(|x: nat, acc: nat| acc * (x as nat), 1) == prod;
        invariant (res.len() == 0) || (res@[(res.len() as int) - 1] as nat <= (f as nat));
        if m % (f as nat) == 0 {
            // f divides m, and by invariant no smaller k in [2, f) divides m,
            // so f is a minimal divisor of m -> prime
            minimal_divisor_is_prime(m, f as nat);
            // push factor f
            let old_prod = prod;
            res.push(f);
            prod = old_prod * (f as nat);
            // update m
            m = m / (f as nat);
        } else {
            // try next candidate
            f = f + 1;
        }
    }

    // After loop, if remaining m > 1, it is prime and should be appended
    if m != 1 {
        // From loop invariant, for all k < f, m % k != 0.
        // Since loop ended with (f as nat) > m, that implies for all 2<=k<m, m%k !=0.
        // Hence m is prime (use minimal_divisor_is_prime with i = m).
        // Note that m % m == 0, and 2 <= m <= m holds if m >= 2.
        minimal_divisor_is_prime(m, m);
        // append final factor m (fits into u8 because orig <= 255)
        let old_prod = prod;
        res.push(m as u8);
        prod = old_prod * m;
        m = 1;
    }

    // At this point prod * m == orig and m == 1, so prod == orig
    assert(prod == orig);
    // Also, res@ fold_right equals prod by loop invariant
    assert(res@.fold_right(|x: nat, acc: nat| acc * (x as nat), 1) == prod);

    // Return the factorization Vec<u8>
    res
    // impl-end
}
```