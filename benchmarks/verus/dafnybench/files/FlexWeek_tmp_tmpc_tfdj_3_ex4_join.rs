use vstd::prelude::*;

verus! {

fn join(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures
        a@ + b@ == c@,
        (a@ + b@).to_multiset() == c@.to_multiset(),
        a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset(),
        a.len() + b.len() == c.len(),

        forall|i: int| 0 <= i < a.len() ==> c[i] == a[i],
        forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() ==> c[i] == b[j],
{
    assume(false);
    unreached()
}

}
fn main() {}