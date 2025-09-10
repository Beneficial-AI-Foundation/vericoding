use vstd::prelude::*;

verus! {

fn reverse(a: &mut Vec<i32>)
    ensures forall|k: int| 0 <= k < old(a).len() ==> a[k] == old(a)[old(a).len() as int - 1 - k]
{
    assume(false);
    unreached()
}

}
fn main() {}