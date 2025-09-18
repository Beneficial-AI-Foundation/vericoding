// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn clip(a: Vec<i32>, min: i32, max: i32) -> (result: Vec<i32>)
    requires min < max,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            if a[i] < min {
                result[i] == min
            } else if a[i] > max {
                result[i] == max
            } else {
                result[i] == a[i]
            }
        }
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