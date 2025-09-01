use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers required for this implementation
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut max = a[0];
    let mut index = 1;
    while index < a.len()
        invariant
            0 <= index <= a.len() as int,
            forall |j: int| #[trigger] (0 <= j < index) ==> a@[j] <= max,
            exists |j: int| #[trigger] (0 <= j < index) && a@[j] == max,
        decreases (a.len() as int - index),
    {
        if a[index] > max {
            max = a[index];
        }
        index += 1;
    }
    assert(forall |i: int| #[trigger] (0 <= i < a.len() as int) ==> a@[i] <= max);
    assert(exists |i: int| #[trigger] (0 <= i < a.len() as int) && a@[i] == max);
    max
}
// </vc-code>

fn main() {}
}