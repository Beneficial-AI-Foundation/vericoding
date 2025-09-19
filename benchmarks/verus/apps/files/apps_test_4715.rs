// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn count_distinct_colors(a: int, b: int, c: int) -> int {
    if a == b && b == c { 1 }
    else if a == b || b == c || a == c { 2 }
    else { 3 }
}

spec fn all_same(a: int, b: int, c: int) -> bool {
    a == b && b == c
}

spec fn exactly_two_same(a: int, b: int, c: int) -> bool {
    (a == b && b != c) || (b == c && a != b) || (a == c && a != b)
}

spec fn all_different(a: int, b: int, c: int) -> bool {
    a != b && b != c && a != c
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        1 <= result as int <= 3,
        result as int == count_distinct_colors(a as int, b as int, c as int),
        result as int == 1 <==> all_same(a as int, b as int, c as int),
        result as int == 2 <==> exactly_two_same(a as int, b as int, c as int),
        result as int == 3 <==> all_different(a as int, b as int, c as int)
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