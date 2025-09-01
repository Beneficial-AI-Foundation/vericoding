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
    let mut i: usize = 0;
    let n = l.len();
    while i < n
        invariant(0 <= i <= n, forall|j: int| 0 <= j < i ==> l[j] < t)
    {
        if l[i] >= t {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>

fn main() {}
}