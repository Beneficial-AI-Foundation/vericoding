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
    let mut i_usize: usize = 1;
    while i_usize < a.len()
        invariant
            i_usize >= 1 && i_usize <= a.len(),
            forall |j: int| 0 <= j < (i_usize as int) ==> a@[j] <= max,
            exists |j: int| 0 <= j < (i_usize as int) && a@[j] == max,
    {
        if a[i_usize] > max {
            max = a[i_usize];
        }
        i_usize = i_usize + 1;
    }
    max
}
// </vc-code>

fn main() {}
}