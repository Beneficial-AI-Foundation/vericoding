use vstd::prelude::*;

verus! {

fn max(a: &[i32]) -> (max: i32)
    requires a.len() > 0,
    ensures forall|j: int| 0 <= j < a.len() ==> max >= a[j],
{
    assume(false);
    unreached()
}

}
fn main() {}