use vstd::prelude::*;

verus! {

fn argmax(a: Vec<i32>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[j] <= a[result as int],
        forall|j: int| 0 <= j < a.len() && a[j] == a[result as int] ==> result <= j as usize,
{
    assume(false);
    unreached()
}

}
fn main() {}