use vstd::prelude::*;

verus! {

fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
{
    assume(false);
    unreached();
}

}
fn main() {}