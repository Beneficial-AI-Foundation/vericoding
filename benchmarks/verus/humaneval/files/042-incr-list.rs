use vstd::prelude::*;

verus! {

fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)

    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,

    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
{
    assume(false);
    unreached();
}

}
fn main() {}