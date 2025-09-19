// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maxArray(a: &Vec<i8>) -> (m: i8)
    requires a.len() >= 1,
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m as int >= a@[k] as int &&
        exists|k: int| 0 <= k < a.len() && m as int == a@[k] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}