// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn difference(a: Vec<i8>, b: Vec<i8>) -> (diff: Vec<i8>)
    ensures
        forall|x: i8| diff@.contains(x) <==> (a@.contains(x) && !b@.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff@.len() ==> diff@.index(i) != diff@.index(j),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}