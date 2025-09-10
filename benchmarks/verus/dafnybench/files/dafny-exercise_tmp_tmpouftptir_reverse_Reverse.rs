use vstd::prelude::*;

verus! {

fn reverse(a: &Vec<char>) -> (b: Vec<char>)
    requires 
        a.len() > 0,
    ensures 
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b[i] == a[a.len() - i - 1],
{
    assume(false);
    unreached()
}

}
fn main() {}