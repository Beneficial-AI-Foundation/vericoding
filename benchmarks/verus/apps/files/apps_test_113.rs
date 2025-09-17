// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: int) -> int
    decreases exp
{
    if exp <= 0 { 1 }
    else { base * power(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: int)
    requires 
        n > 0 && k >= 0,
    ensures 
        result > 0,
        result % n == 0,
        result % power(10, k) == 0,
        forall|m: int| #[trigger] (m % n) == 0 && #[trigger] (m % power(10, k)) == 0 && m > 0 ==> result <= m,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}