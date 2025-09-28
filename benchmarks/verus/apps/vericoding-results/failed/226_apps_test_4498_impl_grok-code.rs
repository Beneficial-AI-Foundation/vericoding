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
/* helper modified by LLM (iteration 5): change exec_dist to return int to avoid underflow */
spec fn dist(p: int, q: int) -> int {
    if p >= q { p - q } else { q - p }
}

fn exec_dist(p: i8, q: i8) -> int {
    if p as int >= q as int { p as int - q as int } else { q as int - p as int }
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
/* code modified by LLM (iteration 5): use int casts for distance calculations to match spec */
{
    let can_direct = exec_dist(a, c) <= d as int;
    let can_via_b = exec_dist(a, b) <= d as int && exec_dist(b, c) <= d as int;
    let can = can_direct || can_via_b;
    if can {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}