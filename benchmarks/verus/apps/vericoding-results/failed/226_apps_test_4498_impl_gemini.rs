// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    (if a - c >= 0 { a - c } else { c - a }) <= d || 
    (((if a - b >= 0 { a - b } else { b - a }) <= d) && 
     ((if b - c >= 0 { b - c } else { c - b }) <= d))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [retained correct helpers for absolute difference] */
spec fn spec_abs_diff(x: int, y: int) -> int {
    if x - y >= 0 { x - y } else { y - x }
}

fn abs_diff(x: i8, y: i8) -> (res: i8)
    requires
        1 <= x as int <= 100,
        1 <= y as int <= 100,
    ensures
        res as int == spec_abs_diff(x as int, y as int),
{
    if x >= y {
        x - y
    } else {
        y - x
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int),
    ensures 
        result@ == seq!['Y', 'e', 's'] <==> can_communicate(a as int, b as int, c as int, d as int),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [add assertions to connect i8 comparisons with int spec] */
{
    let dist_ac = abs_diff(a, c);
    let dist_ab = abs_diff(a, b);
    let dist_bc = abs_diff(b, c);

    assert((dist_ac <= d) <==> (spec_abs_diff(a as int, c as int) <= d as int));
    assert((dist_ab <= d) <==> (spec_abs_diff(a as int, b as int) <= d as int));
    assert((dist_bc <= d) <==> (spec_abs_diff(b as int, c as int) <= d as int));

    if dist_ac <= d || (dist_ab <= d && dist_bc <= d) {
        String::from_str("Yes")
    } else {
        String::from_str("No")
    }
}
// </vc-code>


}

fn main() {}