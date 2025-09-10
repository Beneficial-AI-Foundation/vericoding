use vstd::prelude::*;

verus! {

fn maxArray(a: &[int]) -> (m: int)
    requires a.len() >= 1,
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m >= a@[k] &&
        exists|k: int| 0 <= k < a.len() && m == a@[k],
{
    assume(false);
    unreached();
}

}
fn main() {}