// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, i: int) -> int
    recommends 
        0 <= i < a.len(),
    decreases i
{
    if 0 <= i < a.len() {
        a[i] as int + if i == 0 { 0 } else { sum(a, i - 1) }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cumsum(a: &[i32], b: &mut [i32])
    requires 
        a.len() == old(b).len(),
        a.len() > 0,
    ensures 
        forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}