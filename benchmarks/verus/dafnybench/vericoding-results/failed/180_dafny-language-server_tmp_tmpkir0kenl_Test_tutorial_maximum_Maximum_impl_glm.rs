use vstd::prelude::*;

verus! {

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
// (empty)
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
    let mut max_val: int = values[0];
    let mut i: int = 1;
    while i < values.len()
        invariant
            1 <= i <= values.len(),
            exists |j: int| 0 <= j < i && values[j] == max_val,
            forall |k: int| 0 <= k < i ==> values[k] <= max_val,
        decreases (values.len() - i)
    {
        if values[i] > max_val {
            max_val = values[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>

fn main() {}

}