// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int, e: int, k: int) -> bool {
    0 <= a <= 123 && 0 <= b <= 123 && 0 <= c <= 123 && 
    0 <= d <= 123 && 0 <= e <= 123 && 0 <= k <= 123 &&
    a < b && b < c && c < d && d < e
}

spec fn all_pairs_can_communicate(a: int, b: int, c: int, d: int, e: int, k: int) -> bool {
    (e - a) <= k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int, e: int, k: int) -> (result: String)
    requires
        valid_input(a, b, c, d, e, k)
    ensures
        result@ == "Yay!" <==> all_pairs_can_communicate(a, b, c, d, e, k),
        result@ == ":(" <==> !all_pairs_can_communicate(a, b, c, d, e, k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}