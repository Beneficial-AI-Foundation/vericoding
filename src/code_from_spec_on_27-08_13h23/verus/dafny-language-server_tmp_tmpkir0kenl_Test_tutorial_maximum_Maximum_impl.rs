use vstd::prelude::*;

verus! {

// This file shows how to specify and implement a function to compute the
// largest element of a list. The function is fully specified by two
// preconditions, as proved by the MaximumIsUnique lemma below.

// <vc-helpers>
proof fn maximum_is_unique(values: Seq<int>, max1: int, max2: int)
    requires
        values.len() > 0,
        values.contains(max1),
        values.contains(max2),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max1,
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max2,
    ensures
        max1 == max2,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn maximum(values: Seq<int>) -> (max: int)
    requires
        values.len() > 0,
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn maximum(values: Seq<int>) -> (max: int)
    requires
        values.len() > 0,
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
{
    let mut current_max = values[0];
    let mut index = 1;

    while index < values.len()
        invariant
            0 <= index <= values.len(),
            values.len() > 0,
            forall|i: int| 0 <= i < index ==> values[i] <= current_max,
            values.contains(current_max),
    {
        if values[index] > current_max {
            current_max = values[index];
        }
        index = index + 1;
    }

    current_max
}
// </vc-code>

fn main() {}

}