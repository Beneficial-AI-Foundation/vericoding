// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

spec fn min(x: int, y: int) -> int {
    if x < y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x > y { x } else { y }
}

spec fn interval_overlap_length(a: int, b: int, c: int, d: int) -> int {
    if min(b, d) - max(a, c) > 0 { min(b, d) - max(a, c) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int, d as int),
    ensures
        result >= 0,
        result as int == interval_overlap_length(a as int, b as int, c as int, d as int),
        result <= 100,
// </vc-spec>
// <vc-code>
{
    let start = if a > c { a } else { c };
    let end = if b < d { b } else { d };
    
    if start < end {
        proof {
            assert(start as int == max(a as int, c as int));
            assert(end as int == min(b as int, d as int));
            assert(end - start > 0);
            assert((end - start) as int == min(b as int, d as int) - max(a as int, c as int));
            assert((end - start) as int == interval_overlap_length(a as int, b as int, c as int, d as int));
        }
        end - start
    } else {
        proof {
            assert(start as int == max(a as int, c as int));
            assert(end as int == min(b as int, d as int));
            assert(end as int - start as int <= 0);
            assert(min(b as int, d as int) - max(a as int, c as int) <= 0);
            assert(interval_overlap_length(a as int, b as int, c as int, d as int) == 0);
        }
        0
    }
}
// </vc-code>


}

fn main() {}