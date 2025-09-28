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
/* code modified by LLM (iteration 2): implemented logic using exec arithmetic to compute max distributions */
    let q = n / 3;
    let r = n % 3;
    let result = if r == 0 { 2 * q } else { 2 * q + 1 };
    result
}
// </vc-code>


}

fn main() {}