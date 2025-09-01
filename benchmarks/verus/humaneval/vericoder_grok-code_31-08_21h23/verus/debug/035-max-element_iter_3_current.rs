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
            0 <= index <= a.len(),
            forall |j: int| 0 <= j < index && #[trigger] a.view()[j] ==> a.view()[j] <= max,
            exists |j: int| 0 <= j < index && #[trigger] a.view()[j] && a.view()[j] == max,
    {
        if a[index] > max {
            max = a[index];
        }
        index += 1;
    }
    assert(forall |i: int| 0 <= i < a.len() && #[trigger] a.view()[i] ==> a.view()[i] <= max);
    assert(exists |i: int| 0 <= i < a.len() && #[trigger] a.view()[i] && a.view()[i] == max);
    max
}
// </vc-code>

fn main() {}
}