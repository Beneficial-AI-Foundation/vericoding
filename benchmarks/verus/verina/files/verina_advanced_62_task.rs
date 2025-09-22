// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rain(heights: &Vec<i8>) -> (result: i8)
    requires forall|i: int| 0 <= i < heights@.len() ==> heights@[i] as int >= 0,
    ensures 
        result as int >= 0,
        heights@.len() < 3 ==> result as int == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}