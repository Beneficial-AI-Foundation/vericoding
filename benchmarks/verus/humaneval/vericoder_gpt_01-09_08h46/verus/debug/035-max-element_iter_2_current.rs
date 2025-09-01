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
    let n = a.len();
    let mut i: usize = 1;
    let mut idx: usize = 0;
    while i < n
        invariant
            1 <= i as int <= n as int,
            0 <= idx as int < i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] <= a[idx as int],
        decreases (n as int) - (i as int)
    {
        let old_idx = idx;
        let ai = a[i];
        let gt = ai > a[old_idx];
        if gt {
            idx = i;
        }
        assert forall|j:int| 0 <= j < (i + 1) as int ==> #[trigger] a[j] <= a[idx as int] by {
            if j < i as int {
                if gt {
                    // From invariant: a[j] <= a[old_idx
// </vc-code>

fn main() {}
}