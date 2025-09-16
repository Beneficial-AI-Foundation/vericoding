// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn is_prime(p: u32) -> bool
    recommends
        p > 1,
{
    spec_prime(p as int)
}

/* helper modified by LLM (iteration 5): Fixed exec_is_prime postcondition and overflow checks */
fn exec_is_prime(p: u32) -> (result: bool)
    requires
        p > 1,
    ensures
        result == spec_prime(p as int),
{
    if p == 2 {
        return true;
    }
    if p % 2 == 0 {
        return false;
    }
    let mut d: u32 = 3;
    while d <= p / d
        invariant
            d >= 3,
            d <= p,
            d % 2 == 1,
            forall|k: int| 2 <= k < d ==> #[trigger] (p as int % k) != 0,
        decreases p - d,
    {
        if p % d == 0 {
            return false;
        }
        if d < u32::MAX - 2 {
            d = d + 2;
        } else {
            break;
        }
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)

    requires
        x > 1,

    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow checks and loop bounds */
    let mut i: u32 = 2;
    while i <= x / 2 && i <= x / 2 / 2
        invariant
            i >= 2,
            i <= x,
        decreases x - i,
    {
        if x % i == 0 && i > 1 {
            let q = x / i;
            if q > 1 && exec_is_prime(i) {
                let mut j: u32 = 2;
                while j <= q / 2
                    invariant
                        j >= 2,
                        j <= q / 2 + 1,
                        q == x / i,
                        x % i == 0,
                        i > 1,
                        exec_is_prime(i),
                    decreases q / 2 + 1 - j,
                {
                    if q % j == 0 && j > 1 {
                        let k = q / j;
                        if k > 1 && j <= q / k && exec_is_prime(j) && exec_is_prime(k) {
                            assert(spec_prime(i as int));
                            assert(spec_prime(j as int));
                            assert(spec_prime(k as int));
                            assert(i as int * j as int * k as int == x as int);
                            return true;
                        }
                    }
                    if j < q / 2 {
                        j = j + 1;
                    } else {
                        break;
                    }
                }
            }
        }
        if i < x / 2 {
            i = i + 1;
        } else {
            break;
        }
    }
    false
}
// </vc-code>

}
fn main() {}