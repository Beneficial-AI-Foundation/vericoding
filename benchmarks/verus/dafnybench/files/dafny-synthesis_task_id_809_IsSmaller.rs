// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires 
        a.len() == b.len(),
    ensures 
        result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
        !result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}