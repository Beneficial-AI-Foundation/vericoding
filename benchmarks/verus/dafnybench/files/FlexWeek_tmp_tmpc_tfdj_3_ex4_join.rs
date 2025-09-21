// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn join(a: &[i8], b: &[i8]) -> (c: Vec<i8>)
    ensures
        a@.map(|i: int, x: i8| x as int) + b@.map(|i: int, x: i8| x as int) == c@.map(|i: int, x: i8| x as int),
        (a@.map(|i: int, x: i8| x as int) + b@.map(|i: int, x: i8| x as int)).to_multiset() == c@.map(|i: int, x: i8| x as int).to_multiset(),
        a@.map(|i: int, x: i8| x as int).to_multiset().add(b@.map(|i: int, x: i8| x as int).to_multiset()) == c@.map(|i: int, x: i8| x as int).to_multiset(),
        a.len() + b.len() == c.len(),

        forall|i: int| 0 <= i < a.len() ==> c[i] == a[i],
        forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() ==> c[i] == b[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}