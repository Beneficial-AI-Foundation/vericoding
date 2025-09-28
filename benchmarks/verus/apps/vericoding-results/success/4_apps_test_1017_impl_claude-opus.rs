// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_distributions(n: int) -> int
    recommends valid_input(n)
{
    if n % 3 == 0 { 2 * (n / 3) } else { 2 * (n / 3) + 1 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result >= 1,
        result as int == max_distributions(n as int)
// </vc-spec>
// <vc-code>
{
    let q = n / 3;
    let r = n % 3;
    
    if r == 0 {
        proof {
            assert(n as int == 3 * (q as int));
            assert(max_distributions(n as int) == 2 * (n as int / 3));
            assert(n as int / 3 == q as int);
        }
        2 * q
    } else {
        proof {
            assert(n as int % 3 == r as int);
            assert(r as int != 0);
            assert(max_distributions(n as int) == 2 * (n as int / 3) + 1);
            assert(n as int / 3 == q as int);
        }
        2 * q + 1
    }
}
// </vc-code>


}

fn main() {}