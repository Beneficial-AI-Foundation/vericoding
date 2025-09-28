use vstd::prelude::*;

verus! {

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn maximum(values: Seq<int>) -> (max: int)
    requires
        values.len() > 0,
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
// </vc-spec>
// <vc-code>
{
    let mut max = values[0];
    let mut idx: usize = 1;
    
    while idx < values.len()
        invariant
            0 < idx <= values.len(),
            values.contains(max),
            forall|i: int| 0 <= i < idx ==> values[i] <= max,
    {
        if values[idx as int] > max {
            max = values[idx as int];
        }
        idx = idx + 1;
    }
    
    max
}
// </vc-code>

fn main() {}

}