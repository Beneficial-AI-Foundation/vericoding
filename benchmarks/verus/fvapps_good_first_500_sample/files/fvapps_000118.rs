// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_substring_value(n: u64, m: u64) -> (result: u64)
    requires m <= n,
    ensures
        /* If m=0, result should be 0 */
        m == 0 ==> result == 0,
        /* If m=n, result should be triangular number */
        m == n ==> result == n * (n + 1) / 2,
        /* Output should be between 0 and triangular number */
        0 <= result && result <= n * (n + 1) / 2,
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

fn main() {
    // Test cases from the problem
    // assert(max_substring_value(3, 1) == 4);
    // assert(max_substring_value(3, 2) == 5);
    // assert(max_substring_value(3, 3) == 6);
    // assert(max_substring_value(4, 0) == 0);
    // assert(max_substring_value(5, 2) == 12);
}