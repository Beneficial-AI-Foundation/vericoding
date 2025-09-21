// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i8], b: &[i8]) -> (c: Vec<i8>)
    requires a.len() == b.len()
    ensures 
        c.len() == a.len() && 
        forall |i: int| 0 <= i < c.len() ==> c[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}