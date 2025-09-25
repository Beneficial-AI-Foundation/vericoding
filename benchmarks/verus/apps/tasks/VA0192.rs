// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 2
}

spec fn satisfies_constraint(x: int, n: int, k: int) -> bool {
    x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result > 0,
        satisfies_constraint(result as int, n as int, k as int),
        forall|x: int| #[trigger] satisfies_constraint(x, n as int, k as int) ==> result as int <= x
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}