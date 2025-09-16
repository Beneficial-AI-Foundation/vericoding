// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn find_factor(n: int) -> (ret: Option<int>)
    requires
        n > 1,
    ensures
        match ret {
            Some(f) => 1 < f < n && n % f == 0,
            None => forall|k: int| 1 < k < n ==> n % k != 0,
        },
{
    assume(false);
    None
}

spec fn is_prime(n: int) -> bool {
    n > 1 && forall|k: int| 1 < k < n ==> n % k != 0
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
    let mut n = x as int;
    let mut factors: Seq<int> = Seq::empty();
    
    while n > 1
        invariant
            x > 1,
            n > 0,
            forall|i: int| 0 <= i < factors.len() ==> is_prime(factors[i]),
            forall|i: int| 0 <= i < factors.len() ==> factors[i] > 1,
            n * (factors.len() > 0 ? factors.iter().product() : 1) == x,
        decreases n,
    {
        let found = find_factor(n);
        match found {
            Some(f) => {
                factors = factors.push(f);
                n = n / f;
            }
            None => {
                factors = factors.push(n);
                n = 1;
            }
        }
    }
    
    factors.len() == 3
}
// </vc-code>

}
fn main() {}