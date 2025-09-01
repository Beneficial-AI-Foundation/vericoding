use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
proof fn lemma_is_prime_pred_ge_2(n: u32)
    requires
        is_prime_pred(n),
    ensures
        n >= 2
{
    if n < 2 {
        assert(n < 2);
        assert forall|k: int| 2 <= k < n implies #[trigger] (n as int % k) != 0 by {
            // vacuously true since no k satisfies 2 <= k < n
        }
        assert(is_prime_pred(n));
    }
}

proof fn lemma_prime_divisor_has_prime_factor(p: u32, n: u32)
    requires
        is_prime_pred(p),
        2 <= n < p * p,
        (n as int) % (p as int) == 0,
    ensures
        1 <= n / p < p,
        exists|q: u32| 1 <= q <= n / p && is_prime_pred(q) && (n as int) % (q as int) == 0
{
    let q = n / p;
    assert(q * p == n);
    assert(q >= 1);
    assert(q < p);
    if !is_prime_pred(q) {
        assert(exists(|k: int| 2 <= k < q && (q as int % k) == 0));
        let k = choose(|k: int| 2 <= k < q && (q as int % k) == 0);
        assert((n as int) % k == (q * p as int) % k == ((q as int % k) * (p as int % k)) % k == 0);
        assert(2 <= k < q < p);
        assert((n as int) % k == 0);
        assert((p as int) % k != 0);
        lemma_prime_divisor_has_prime_factor(p, k);
        let r = choose(|r: u32| 1 <= r <= k && is_prime_pred(r) && (k as int) % (r as int) == 0);
        assert(r <= k < p);
        assert(is_prime_pred(r));
        assert((n as int) % (r as int) == (k as int) % (r as int) == 0);
        assert(r <= n / p);
    }
}

proof fn lemma_prime_factorization(n: u32)
    requires
        2 <= n,
    ensures
        exists|p: u32| 1 <= p <= n && is_prime_pred(p) && (n as int) % (p as int) == 0
{
    if is_prime_pred(n) {
        assert((n as int) % (n as int) == 0);
    } else {
        assert(exists(|k: int| 2 <= k < n && (n as int % k) == 0));
        let k = choose(|k: int| 2 <= k < n && (n as int % k) == 0);
        assert(k <= n);
        lemma_prime_factorization(k);
        let p = choose(|p: u32| 1 <= p <= k && is_prime_pred(p) && (k as int) % (p as int) == 0);
        assert((n as int) % (p as int) == (k * (n/k) as int) % p == ((k as int % p) * ((n/k) as int % p)) % p == 0);
    }
}

proof fn lemma_largest_prime_factor_le_sqrt(n: u32, p: u32)
    requires
        2 <= n,
        is_prime_pred(p),
        (n as int) % (p as int) == 0,
        forall|k: u32| (p as int) < k <= (n as int).sqrt() ==> !is_prime_pred(k) || (n as int) % (k as int) != 0,
    ensures
        p >= (n as int).sqrt() as u32 || p == n
{
    let sqrt_n = (n as int).sqrt() as u32;
    if p < sqrt_n {
        let q = n / p;
        assert(q > p);
        assert(q <= n / p);
        if q <= n / p && q > p {
            lemma_prime_factorization(q);
            let r = choose(|r: u32| 1 <= r <= q && is_prime_pred(r) && (q as int) % (r as int) == 0);
            assert((n as int) % (r as int) == 0);
            assert(r <= q <= n / p);
            if r <= sqrt_n {
                assert(r > 1);
                lemma_is_prime_pred_ge_2(r);
                assert forall|k: int| 2 <= k < r implies #[trigger] (r as int % k) != 0 by {
                    if 2 <= k < r {
                        assert((r as int) % k != 0);
                    }
                }
                assert(is_prime_pred(r));
                assert(false);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    let mut n = n;
    let mut largest_factor = 1;
    let mut f = 2;
    
    while f * f <= n
        invariant
            1 <= largest_factor <= n,
            f >= 2,
            (f * f <= n && largest_factor >= 1) || (f * f > n && largest_factor >= f - 1),
            largest_factor == 1 || is_prime_pred(largest_factor),
            exists|k: u32| 1 <= k <= n && is_prime_pred(k) && (n as int) % (k as int) == 0,
            n == 1 || (forall|k: u32| 2 <= k < f ==> (n as int) % (k as int) != 0 || (n as int) % (k as int) == 0 && k <= largest_factor)
    {
        if (n as int) % (f as int) == 0 {
            lemma_prime_factorization(f);
            let p = choose(|p: u32| 1 <= p <= f && is_prime_pred(p) && (f as int) % (p as int) == 0);
            assert(p <= f);
            assert(p >= 2);
            assert forall|k: int| 2 <= k < p implies #[trigger] (p as int % k) != 0 by {
                if 2 <= k < p {
                    assert((p as int) % k != 0);
                }
            }
            assert(is_prime_pred(p));
            largest_factor = p;
            n = n / f;
        } else {
            f = f + 1;
        }
    }
    
    if n > 1 {
        if largest_factor < n {
            lemma_prime_factorization(n);
            assert forall|k: int| 2 <= k < n implies #[trigger] (n as int % k) != 0 by {
                if 2 <= k < n {
                    assert(k >= f);
                }
            }
            assert(is_prime_pred(n));
            largest_factor = n;
        }
    }
    
    largest_factor
}
// </vc-code>

fn main() {}
}