use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
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
    let mut i: nat = 1;
    let mut max: i32 = a[0];
    while (i < a.len())
        invariant i <= a.len();
        invariant forall |j: nat| j < i ==> #[trigger] a[j] <= max;
        invariant exists |j: nat| j < i && #[trigger] a[j] == max;
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

fn main() {}
}