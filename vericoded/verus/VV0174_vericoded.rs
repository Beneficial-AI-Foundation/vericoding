// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// no helpers
// </vc-helpers>

// <vc-spec>
fn iter_copy(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == result[i],
// </vc-spec>
// <vc-code>
{
    let result = s.clone();
    result
}
// </vc-code>

}
fn main() {}