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
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        n > 0 && k >= 0,
    ensures 
        result > 0,
        (result as int) % (n as int) == 0,
        (result as int) % power(10, k as int) == 0,
        forall|m: int| #[trigger] (m % (n as int)) == 0 && #[trigger] (m % power(10, k as int)) == 0 && m > 0 ==> (result as int) <= m,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}