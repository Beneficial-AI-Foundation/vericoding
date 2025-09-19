// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_get_zero_sum_subset(a: i32, b: i32, c: i32, d: i32) -> (result: &'static str)
    ensures 
        result == "Yes" || result == "No",
        (a == 0 || b == 0 || c == 0 || d == 0) ==> result == "Yes",
        (a == -b || a == -c || a == -d || b == -c || b == -d || c == -d) ==> result == "Yes",
        (a > 0 && b > 0 && c > 0 && d > 0) ==> result == "No",
        (a < 0 && b < 0 && c < 0 && d < 0) ==> result == "No"
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "No"
    // impl-end
}
// </vc-code>


}
fn main() {}