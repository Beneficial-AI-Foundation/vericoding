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
    let mut max: int = values@[0];
    let mut i: int = 1int;

    while i < values.len()
        invariant
            0 <= i <= values.len(),
            values.contains(max),
            forall|j: int| 0 <= j < i ==> #[trigger] (values[j]) values[j] <= max,
    {
        if values@[i] > max {
            max = values@[i];
        }
        i = i + 1int;
    }

    max
}
// </vc-code>

fn main() {}

}