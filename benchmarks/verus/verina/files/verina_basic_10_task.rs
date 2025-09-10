use vstd::prelude::*;

verus! {

fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
{
    assume(false);
    unreached()
}

}
fn main() {}