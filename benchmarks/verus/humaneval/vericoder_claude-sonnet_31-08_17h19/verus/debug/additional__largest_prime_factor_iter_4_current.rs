use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
spec fn divides(a: int, b: int) -> bool {
    b != 0 && a % b == 0
}

spec fn has_factor_in_range(n: int, start: int, end: int) -> bool {
    exists|k: int| start <= k <= end && divides(n, k)
}

proof fn prime_has_no_small_factors(p: int)
    requires
        p >= 2,
        p <= u32::MAX,
        is_prime_pred(p as u32),
    ensures
        forall|k: int| 2 <= k < p ==> !divides(p, k)
{
    assert forall|k: int| 2 <= k < p implies !divides(p, k) by {
        if divides(p, k) {
            assert((p % k) == 0);
            assert((p as u32 % k as u32) != 0); // from is_prime_pred contradiction
            assert(false);
        }
    }
}

proof fn divisor_bounds(n: int, d: int)
    requires
        n > 1,
        d > 1,
        divides(n, d)
    ensures
        d <= n
{
    assert(n % d == 0);
    assert(n >= d);
}

proof fn one_is_prime_vacuous()
    ensures is_prime_pred(1)
{
    assert forall|k: int| 2 <= k < 1 implies #[trigger] (1int % k) != 0 by {
        // vacuously true since 2 <= k < 1 is impossible
    }
}

proof fn current_has_prime_factor(n: u32, current: u32)
    requires
        n >= 2,
        current > 1,
        current <= n,
        divides(n as int, current as int),
    ensures
        exists|p: int| 1 < p <= current && divides(current as int, p) && 2 <= p <= u32::MAX && is_prime_pred(p as u32),
{
    let mut c = current as int;
    let mut f = 2;
    
    while f * f <= c && c > 1
        invariant
            1 < c <= current,
            2 <= f,
            forall|k: int| 2 <= k < f ==> !divides(c, k),
        decreases c
    {
        if c % f == 0 {
            assert(divides(c, f));
            assert(is_prime_pred(f as u32));
            return;
        }
        f = f + 1;
    }
    
    if c > 1 {
        assert(c <= u32::MAX);
        assert(is_prime_pred(c as u32));
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
    if n == 1 {
        proof { one_is_prime_vacuous(); }
        return 1;
    }
    
    let mut largest_factor = 1u32;
    let mut current = n;
    let mut factor = 2u32;
    
    proof {
        current_has_prime_factor(n, current);
    }
    
    while factor <= 46340 && #[verifier::truncate] factor * factor <= current && current > 1
        invariant
            2 <= factor,
            1 <= current <= n,
            largest_factor <= n,
            largest_factor == 1 || (largest_factor > 1 && 2 <= largest_factor <= u32::MAX && is_prime_pred(largest_factor)),
            current > 1 ==> exists|p: int| p > largest_factor && 1 < p <= current && divides(current as int, p) && 2 <= p <= u32::MAX && is_prime_pred(#[verifier::truncate] p as u32),
            divides(n as int, current as int),
        decreases current, 46341 - factor
    {
        if current % factor == 0 {
            largest_factor = factor;
            while current % factor == 0 && current > 1
                invariant
                    2 <= factor,
                    1 <= current <= n,
                    largest_factor == factor,
                    largest_factor > 1 && 2 <= largest_factor <= u32::MAX && is_prime_pred(largest_factor),
                    divides(n as int, current as int),
                decreases current
            {
                current = current / factor;
            }
        }
        factor = factor + 1;
    }
    
    if current > 1 {
        largest_factor = current;
    }
    
    if largest_factor == 1 {
        proof { one_is_prime_vacuous(); }
    }
    
    largest_factor
}
// </vc-code>

fn main() {}
}