// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_impact_points(n: u32, k: u32, m: u64, x0: i64) -> (result: String)
    requires 
        1 <= n && n <= 100,
        1 <= k && k <= 1000,
        1 <= m && m <= 1000000000000000000u64,
        -1000000000i64 <= x0 && x0 <= 1000000000i64,
    ensures
        equal(result@, seq!['y', 'e', 's']) || equal(result@, seq!['n', 'o']),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "no".to_string()
    // impl-end
}
// </vc-code>


}
fn main() {}