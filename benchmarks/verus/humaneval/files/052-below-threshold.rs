use vstd::prelude::*;

verus! {

fn below_threshold(l: &[i32], t: i32) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
{
    assume(false);
    unreached()
}

}
fn main() {}