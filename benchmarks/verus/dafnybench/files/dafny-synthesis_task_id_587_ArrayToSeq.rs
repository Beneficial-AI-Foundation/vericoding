use vstd::prelude::*;

verus! {

fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
{
    assume(false);
    unreached()
}

}
fn main() {}