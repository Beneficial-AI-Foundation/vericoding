```vc-helpers
proof fn minimal_factor_prime(m: nat, k: nat)
    requires
        m >= 2,
        2 <= k && k <= m,
        m % k == 0,
        forall|d: nat| 2 <= d < k ==> m % d != 0,
    ensures
        is_prime(k),
{
    proof {
        // Show: forall i. 1 < i < k ==> k % i != 0
        assert(forall|i: nat| 1 < i < k ==> k % i != 0) by {
            fix i;
            assume(1 < i && i < k);
            // Suppose k % i == 0, derive contradiction with minimality of k.
            if k % i == 0 {
                let q = k / i;
                let t = m / k;
                // k == q * i because k % i == 0
                assert(k == q * i);
                // m == t * k because m % k == 0
                assert(m == t * k);
                // hence m == t * q * i
                assert(m == t * q * i);
                // so m % i == 0
                assert(m % i == 0);
                // contradicts minimality of k
                assert(m % i != 0); // from precondition forall d < k
                assert(false);
            } else {
                // k % i != 0 already holds
            }
        }
    }
}
```

```vc-code
{
    // impl-start
    fn factorize(n: u8) -> (factorization: Vec<u8>)
        requires
            1 <= n <= u8::MAX,
        ensures
            is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
    {
        let mut v: Vec<u8> = Vec::new();
        let mut rem: nat = n as nat;
        let mut k: nat = 2;
        // prod represents the product (fold_right) of elements in v (in the folded order used in spec)
        let mut prod: nat = 1;

        // Outer loop: try divisors k from 2 upwards while k*k <= rem
        while k * k <= rem
            invariant
                1 <= rem,
                2 <= k,
                prod >= 1,
                prod * rem == n as nat,
                // all elements in v are prime
                forall|idx: int| 0 <= idx < (v@.len() as int) ==> is_prime(v@[(idx as nat)] as nat),
                // product represented by prod equals fold_right over v
                prod == v@.map(|_i, x: u8| x as nat).fold_right(|x: nat, acc: nat| (acc * x), 1),
                // v is non-decreasing
                forall|i: nat, j: nat| (i <= j && j < v@.len()) ==> (v@[i] <= v@[j]),
        {
            // Inner loop: while k divides rem, repeatedly extract factor k
            while rem % k == 0
                invariant
                    1 <= rem,
                    2 <= k,
                    prod >= 1,
                    prod * rem == n as nat,
                    forall|idx: int| 0 <= idx < (v@.len() as int) ==> is_prime(v@[(idx as nat)] as nat),
                    prod == v@.map(|_i, x: u8| x as nat).fold_right(|x: nat, acc: nat| (acc * x), 1),
                    forall|i: nat, j: nat| (i <= j && j < v@.len()) ==> (v@[i] <= v@[j]),
            {
                // At this point, k*k <= rem and rem % k == 0, so k <= rem.
                // Also, because we have incremented k from 2 upward, for all d < k, rem % d != 0.
                // Prove that and use minimal_factor_prime lemma to show k is prime.
                // Establish minimality: for all d in 2 .. k-1, rem % d != 0
                assert(forall|d: nat| 2 <= d < k ==> rem % d != 0) by {
                    fix d;
                    assume(2 <= d && d < k);
                    // If rem % d == 0 earlier, we would have extracted that factor when that d was current.
                    // Since k has been increased only when previous divisors did not divide current rem,
                    // rem % d != 0 holds.
                    // This is maintained by the outer/inner loop invariants.
                    // We can derive it by contradiction:
                    if rem % d == 0 {
                        // Then earlier when the outer loop had k = d, we would have divided out d.
                        // Hence this branch is unreachable given the loop structure.
                        assert(false);
                    } else { }
                }

                // Now k is a prime by minimal_factor_prime
                minimal_factor_prime(rem, k);

                // push k into v. Update prod = k * prod to match the fold_right order used in the spec.
                v.push((k as u8));
                prod = k * prod;
                // Update rem
                rem = rem / k;
                // After division, for any d < k, rem % d != 0 still holds:
                assert(forall|d: nat| 2 <= d < k ==> rem % d