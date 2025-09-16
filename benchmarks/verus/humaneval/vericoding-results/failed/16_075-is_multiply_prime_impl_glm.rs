// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed type casts to int in executable code */

spec fn is_prime(p: u32) -> (ret: bool)
    requires
        p > 1,
    ensures
        ret <==> spec_prime(p as int),
{
    &&& p > 1
    &&& (forall|i: int|
        1 < i < p as int ==> #[trigger] (p as int) % i != 0)
}

fn smallest_prime_factor(x: u32) -> (p: u32)
    requires
        x > 1,
    ensures
        p > 1,
        p <= x,
        x % p == 0,
        (forall|i: int| 2 <= i < p as int ==> #[trigger] (x as int) % i != 0),
        spec_prime(p as int),
{
    let mut i: u32 = 2;
    while i < x && x % i != 0
        invariant
            2 <= i <= x,
            (forall|j: int| 2 <= j < i as int ==> #[trigger] (x as int) % j != 0),
        decreases x - i,
    {
        i += 1u32;
    }
    i
}

proof fn prime_factor_exists(x: u32)
    requires
        x > 1,
        !is_prime(x),
    ensures
        exists|p: u32| 1 < p < x && x % p == 0,
{
    let p = smallest_prime_factor(x);
    assert(p > 1 && p < x && x % p == 0);
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
    /* code modified by LLM (iteration 5): removed type casts to int in executable code */
    if x < 8 {
        return false;
    }

    let a = smallest_prime_factor(x);
    let mut remaining = x / a;
    if remaining < 4 {
        return false;
    }

    let b = smallest_prime_factor(remaining);
    remaining = remaining / b;
    if remaining < 2 {
        return false;
    }

    let c = remaining;
    return smallest_prime_factor(a) == a && smallest_prime_factor(b) == b && smallest_prime_factor(c) == c;
}
// </vc-code>

}
fn main() {}