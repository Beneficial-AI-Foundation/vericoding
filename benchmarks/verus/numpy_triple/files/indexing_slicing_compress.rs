// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int
    decreases condition.len()
{
    if condition.len() == 0 {
        0
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn compress(condition: Vec<bool>, a: Vec<f32>) -> (result: Vec<f32>)
    requires condition.len() == a.len(),
    ensures
        result.len() == count_true(condition@),
        exists|mapping: Seq<int>|
            mapping.len() == result.len() &&
            (forall|i: int| 0 <= i < mapping.len() ==> 
                0 <= mapping[i] < condition.len() &&
                condition@[mapping[i]] == true) &&
            (forall|i: int| 0 <= i < result.len() ==> 
                result@[i] == a@[mapping[i]]) &&
            (forall|i: int, j: int| 0 <= i < j < mapping.len() ==> 
                mapping[i] < mapping[j]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}