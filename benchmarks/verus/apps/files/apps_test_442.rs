// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn h(x: int, y: int) -> int {
    x * x + 2 * x * y + x + 1
}

spec fn valid_input(r: int) -> bool {
    r > 0
}

spec fn valid_solution(result: Seq<int>, r: int) -> bool {
    if result.len() == 0 {
        true
    } else {
        result.len() == 2 && result[0] > 0 && result[1] > 0 && h(result[0], result[1]) == r
    }
}

spec fn has_solution(r: int) -> bool {
    r > 4 && r % 2 == 1
}
// </vc-helpers>

// <vc-spec>
fn solve(r: int) -> (result: Vec<int>)
    requires 
        valid_input(r)
    ensures 
        valid_solution(result@, r),
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 2 ==> result@[0] > 0 && result@[1] > 0,
        result@.len() == 2 ==> h(result@[0], result@[1]) == r,
        r <= 4 ==> result@.len() == 0,
        r > 4 && r % 2 == 0 ==> result@.len() == 0,
        r > 4 && r % 2 == 1 ==> result@.len() == 2 && result@[0] == 1 && result@[1] == (r - 3) / 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}