// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn clip(a: Vec<i8>, min: i8, max: i8) -> (result: Vec<i8>)
    requires min < max,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> {
            if a@[i] < min as int {
                result@[i] == min as int
            } else if a@[i] > max as int {
                result@[i] == max as int
            } else {
                result@[i] == a@[i]
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