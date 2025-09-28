// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn lucas(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        2
    } else if n == 1 {
        1
    } else {
        lucas(n - 1) + lucas(n - 2)
    }
}

spec fn valid_input(n: int) -> bool {
    1 <= n <= 86
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lucas_exec helper to compute Lucas number */
fn lucas_exec(n: int) -> int
    requires n >= 0
    decreases n
    ensures result == lucas(n)
{
    if n <= 0 {
        2
    } else if n == 1 {
        1
    } else {
        lucas_exec(n - 1) + lucas_exec(n - 2)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == lucas(n as int)
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 5): replaced assume with actual computation */
    let result = lucas_exec(n as int) as i8;
    result
}
// </vc-code>


}

fn main() {}