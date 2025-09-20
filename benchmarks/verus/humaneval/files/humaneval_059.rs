// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n > 1 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn power_of_2_factor(n: int, current: int) -> int
    recommends n > 0 && current > 0
    decreases current
    when current > 0
{
    if current % 2 != 0 { 1 }
    else { 2 * power_of_2_factor(n, current / 2) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: i8) -> (result: i8)
    requires 
        n as int > 1,
        !is_prime(n as int),
    ensures 
        result as int > 1,
        (n as int) % (result as int) == 0,
        forall|k: int| k > result as int && (n as int) % k == 0 ==> !is_prime(k),
        is_prime(result as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}