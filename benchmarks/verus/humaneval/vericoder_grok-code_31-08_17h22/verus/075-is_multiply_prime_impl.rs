use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
use vstd::math::*;

fn is_prime(p: u32) -> (ret: bool)
    requires
        p > 1,
    ensures
        ret <==> forall|k: int| 1 < k < p ==> #[trigger] (p as int % k) != 0,
{
    let sq = isqrt(p as int) as u32;
    for k in 2..=sq {
        if p % k == 0 {
            return false;
        }
    }
    true
}

fn max_candidate(x: u32) -> u32
    ensures
        forall|i: int| 2 <= i <= (max_candidate(x) as int) ==> i * i * i <= x,
        forall|i: int| i * i * i <= x ==> i <= max_candidate(x as int) + 1,
{
    let mut max_ = 1;
    proof {
        assert(2 <= 2);
        assert(forall|i: int| 1 < i < 2 ==> i * i * i <= 1 ==> false) by (prover_auto);
    }
    for i in 2..=2000 {
        if (i as int) * (i as int) * (i as int) <= x as int {
            max_ = i;
            proof {
                assert((i as int) * (i as int) * (i as int) <= x as int);
            }
        }
    }
    max_
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)
    // pre-conditions-start
    requires
        x > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn is_multiply_prime(x: u32) -> (ans: bool)
    // pre-conditions-start
    requires
        x > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
    // post-conditions-end

{
    let max_p = max_candidate(x);
    for a in 2..=max_p {
        if is_prime(a) && x % a == 0 {
            let rem1 = x / a;
            for b in a..=max_p {
                if is_prime(b) && rem1 % b == 0 {
                    let rem2 = rem1 / b;
                    if is_prime(rem2) {
                        return true;
                    }
                }
            }
        }
    }
    false
}
// </vc-code>

fn main() {}
}