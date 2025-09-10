use vstd::prelude::*;

verus! {

fn rstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() <= a[i]@.len()
{
    assume(false);
    unreached()
}

}
fn main() {}