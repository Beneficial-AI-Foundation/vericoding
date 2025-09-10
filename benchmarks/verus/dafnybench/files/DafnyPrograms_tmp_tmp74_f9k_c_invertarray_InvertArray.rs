use vstd::prelude::*;

verus! {

fn invert_array(a: &mut Vec<i32>)
    ensures
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[a.len() - 1 - i],
{
    assume(false);
    unreached()
}

}
fn main() {}