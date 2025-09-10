use vstd::prelude::*;

verus! {

fn strip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| #[trigger] result[i] == result[i] && 0 <= i < a.len() ==> {
            let original = a[i];
            let res = result[i];
            res@.len() <= original@.len() &&
            (original@.len() == 0 ==> res@.len() == 0)
        }
{
    assume(false);
    unreached();
}

}
fn main() {}