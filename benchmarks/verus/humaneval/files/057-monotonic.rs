use vstd::prelude::*;

verus! {

fn monotonic(l: Vec<i32>) -> (ret: bool)

    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
{
    assume(false);
    unreached()
}

}
fn main() {}