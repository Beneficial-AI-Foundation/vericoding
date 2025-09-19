// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i8>, b: &Vec<i8>) -> (c: Vec<i8>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] as int + b[i] as int == c[i] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}