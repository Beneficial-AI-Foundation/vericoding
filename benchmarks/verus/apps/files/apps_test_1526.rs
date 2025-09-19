// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    0 <= a <= 50 && 0 <= b <= 50 && 0 <= c <= 50
}

spec fn max_of_3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a }
    else if b >= c { b }
    else { c }
}

spec fn sort_descending(a: int, b: int, c: int) -> (int, int, int) {
    if a >= b && a >= c {
        if b >= c { (a, b, c) } else { (a, c, b) }
    } else if b >= a && b >= c {
        if a >= c { (b, a, c) } else { (b, c, a) }
    } else {
        if a >= b { (c, a, b) } else { (c, b, a) }
    }
}

spec fn min_operations(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let (a0, a1, a2) = sort_descending(a, b, c);
    let gap1 = a0 - a1;
    let updated_smallest = a2 + gap1;
    let remaining_gap = a0 - updated_smallest;
    gap1 + remaining_gap / 2 + (remaining_gap % 2) * 2
}

spec fn all_equal(a: int, b: int, c: int) -> bool {
    a == b && b == c
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int),
    ensures
        result >= 0,
        all_equal(a as int, b as int, c as int) ==> result == 0,
        result as int == min_operations(a as int, b as int, c as int),
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