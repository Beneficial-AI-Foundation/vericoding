// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn all_remainders_distinct(n: int, k: int) -> bool
    recommends valid_input(n, k)
{
    forall|i: int| 1 <= i <= k ==> n % i == (i - 1)
}

spec fn has_non_distinct_remainder(n: int, k: int) -> bool
    recommends valid_input(n, k)
{
    exists|i: int| 1 <= i <= k && n % i != (i - 1)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: String)
    requires 
        valid_input(n, k)
    ensures 
        result@ == "Yes\n" <==> all_remainders_distinct(n, k),
        result@ == "No\n" <==> has_non_distinct_remainder(n, k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}