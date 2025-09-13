// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<int>, input: Seq<char>) -> bool {
    result.len() >= 0 &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] >= 1) &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] <= result.len())
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<int>)
    requires valid_input(input)
    ensures valid_output(result, input)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}