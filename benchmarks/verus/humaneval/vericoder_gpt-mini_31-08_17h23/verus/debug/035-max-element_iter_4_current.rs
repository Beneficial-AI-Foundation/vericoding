use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    // impl-start
    let n: nat = a.len();
    let mut idx: nat = 1;
    let mut current: i32 = a@[0];

    while idx < n
        invariant idx <= n;
        invariant forall |j: int| 0 <= j && j < (idx as int) ==> a@[j] <= current;
        invariant exists |j: int| 0 <= j && j < (idx as int) && a@[j] == current;
        decreases n - idx
    {
        let v: i32 = a@[idx as int];
        if v > current {
            current = v;
        }
        idx = idx + 1;
    }

    current
    // impl-end
}
// </vc-code>

fn main() {}
}