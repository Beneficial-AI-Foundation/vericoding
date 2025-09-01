use vstd::prelude::*;

verus! {

// <vc-helpers>
fn max_from(a: &Vec<i32>, start: nat) -> (res: i32)
    requires
        start < a.len(),
    ensures
        forall |i: nat| start <= i < a.len() ==> a[i] <= res,
        exists |i: nat| start <= i < a.len() && a[i] == res,
    decreases
        a.len() - start
{
    if start + 1 == a.len() {
        a[start]
    } else {
        let tail_max = max_from(a, start + 1);
        if a[start] >= tail_max {
            a[start]
        } else {
            tail_max
        }
    }
}
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
    max_from(a, 0)
}
// </vc-code>

fn main() {}
}