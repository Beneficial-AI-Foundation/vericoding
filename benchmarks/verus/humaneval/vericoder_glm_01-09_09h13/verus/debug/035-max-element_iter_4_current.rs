use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut i: int = 1;
    while i < a.len() as int
        invariant
            1 <= i <= a.len() as int,
            forall |j: int| 0 <= j < i ==> a@[j] <= max,
            exists |j: int| 0 <= j < i && a@[j] == max,
    {
        if a@[i] > max {
            max = a[i as usize];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

fn main() {}
}