use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = l.len();
    let mut i: usize = 0;
    while i < n {
        invariant (forall |j: int| 0 <= j && j < (i as int) ==> l[j as usize] < t);
        if l[i as usize] >= t {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {}
}