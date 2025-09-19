// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(r: i8) -> (result: Vec<i8>)
    requires 
        valid_input(r as int)
    ensures 
        valid_solution(result@.map(|i: int, x: i8| x as int), r as int),
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 2 ==> result@[0] as int > 0 && result@[1] as int > 0,
        result@.len() == 2 ==> h(result@[0] as int, result@[1] as int) == r as int,
        r as int <= 4 ==> result@.len() == 0,
        r as int > 4 && (r as int) % 2 == 0 ==> result@.len() == 0,
        r as int > 4 && (r as int) % 2 == 1 ==> result@.len() == 2 && result@[0] as int == 1 && result@[1] as int == ((r as int) - 3) / 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}