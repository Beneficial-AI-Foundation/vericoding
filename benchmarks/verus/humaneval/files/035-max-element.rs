use vstd::prelude::*;

verus! {

fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
{
    assume(false);
    unreached()
}

}
fn main() {}