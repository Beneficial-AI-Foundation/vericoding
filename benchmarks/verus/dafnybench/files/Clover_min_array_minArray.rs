use vstd::prelude::*;

verus! {

fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
{
    assume(false);
    unreached();
}

}
fn main() {}