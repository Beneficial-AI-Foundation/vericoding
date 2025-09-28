use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn divides(a: int, b: int) -> bool
    recommends a != 0
{
    b % a == 0
}

proof fn prime_divisor_lemma(n: int, k: int)
    requires
        n >= 2,
        k > 0,
        k < n,
        divides(k, n),
    ensures
        exists|d: int| 2 <= d * d <= n && divides(d, n)
{
    if k >= 2 {
        assert(divides(k, n));
        assert(k >= 2 && k * k <= n || exists|d: int| 2 <= d * d <= n && divides(d, n));
    } else {
        let m = n / k;
        assert(m >= 2 && m < n);
        assert(divides(m, n));
        assert(m * m <= n || exists|d: int| 2 <= d * d <= n && divides(d, n));
    }
}

spec fn has_divisor(n: int, low: int, high: int) -> bool
    recommends low > 0, high >= low
{
    exists|k: int| low <= k <= high && divides(k, n)
}

proof fn prime_check_range_lemma(n: int)
    requires n >= 2
    ensures
        (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0) ==
        !has_divisor(n, 2, n - 1)
{
}

proof fn sqrt_bound_lemma(n: int)
    requires n >= 2
    ensures
        exists|k: nat| k >= 1 && k * k <= n && (k + 1) * (k + 1) > n
{
}

spec fn sqrt_upper_bound(n: int) -> nat
    recommends n >= 2
{
    choose|k: nat| k >= 1 && k * k <= n && (k + 1) * (k + 1) > n
}

proof fn divisors_preserved_lemma(n: int, bound: int)
    requires n >= 2, bound >= 1, bound * bound <= n
    ensures
        has_divisor(n, 2, n - 1) <==> has_divisor(n, 2, bound)
{
    if has_divisor(n, 2, n - 1) {
        let d = choose|d: int| 2 <= d <= n - 1 && divides(d, n);
        if d * d <= n {
            assert(has_divisor(n, 2, bound));
        } else {
            let m = n / d;
            assert(m >= 2 && m < d);
            assert(divides(m, n));
            assert(has_divisor(n, 2, bound));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    proof {
        sqrt_bound_lemma(n);
    }
    let bound: nat = sqrt_upper_bound(n);
    proof {
        assert(bound >= 1 && bound * bound <= n);
    }
    let mut i: int = 2;
    while i <= bound as int
        invariant
            2 <= i <= bound as int + 1,
            forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0,
        decreases bound as int + 1 - i
    {
        if n % i == 0 as int {
            proof {
                prime_check_range_lemma(n);
                divisors_preserved_lemma(n, bound as int);
                assert(has_divisor(n, 2, bound as int));
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        prime_check_range_lemma(n);
        divisors_preserved_lemma(n, bound as int);
        assert(!has_divisor(n, 2, bound as int) ==> !has_divisor(n, 2, n - 1));
    }
    true
}
// </vc-code>

fn main() {
}

}