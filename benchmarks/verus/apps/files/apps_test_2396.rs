// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<int>, input: Seq<char>) -> bool {
    result.len() >= 0 &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] >= 1) &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] <= result.len())
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<i8>)
    requires valid_input(input@)
    ensures valid_output(result@.map(|i: int, x: i8| x as int), input@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}