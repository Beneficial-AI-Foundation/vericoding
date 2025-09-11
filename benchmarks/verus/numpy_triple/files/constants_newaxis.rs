// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn expand_to_column<T>(v: Vec<T>, axis: NewAxis) -> (result: Vec<Vec<T>>)
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            result[i].len() == 1 &&
            result[i][0] == v[i]
        ),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}