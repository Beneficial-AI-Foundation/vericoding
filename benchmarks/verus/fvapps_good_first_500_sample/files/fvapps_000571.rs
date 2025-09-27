// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_boy_strengths(n: usize, girls: Vec<u32>) -> (result: Vec<u32>)
    requires n > 0,
    ensures
        result.len() == girls.len(),
        forall|x: u32| #[trigger] result@.contains(x) ==> x >= 0,
        forall|i: int| 0 <= i < girls.len() ==> {
            let girl = #[trigger] girls[i];
            let boy = result[i];
            if girl == 2 {
                boy == 1
            } else {
                boy == (girl ^ 2)
            }
        },
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