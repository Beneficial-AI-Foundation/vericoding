use vstd::prelude::*;

verus! {

fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
{
    let mut idx = 0;
    while idx < l.len()
        invariant
            0 <= idx <= l.len(),
            forall|i: int| 0 <= i < idx ==> l[i] < t,
    {
        if l[idx] >= t {
            return false;
        }
        idx += 1;
    }
    true
}

}
fn main() {}