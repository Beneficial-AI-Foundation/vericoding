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
fn exec_min(x: i8, y: i8) -> (result: i8)
    ensures
        result as int == min(x as int, y as int),
{
    if x < y { x } else { y }
}

fn exec_max(x: i8, y: i8) -> (result: i8)
    ensures
        result as int == max(x as int, y as int),
{
    if x > y { x } else { y }
}
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
    let max_ac = exec_max(a, c);
    let min_bd = exec_min(b, d);
    
    let overlap = min_bd - max_ac;

    if overlap > 0 {
        overlap
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}