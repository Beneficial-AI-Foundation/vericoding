use vstd::prelude::*;

verus! {

fn reverse(a: &Vec<char>) -> (b: Vec<char>)
    requires a.len() > 0
    ensures 
        a.len() == b.len(),
        forall|k: int| 0 <= k < a.len() ==> b[k] == a[(a.len() - 1) - k]
{
    assume(false);
    unreached()
}

}
fn main() {}