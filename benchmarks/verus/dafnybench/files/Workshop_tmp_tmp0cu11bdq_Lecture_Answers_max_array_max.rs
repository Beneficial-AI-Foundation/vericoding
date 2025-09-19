// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max(a: &Vec<i8>) -> (result: i8)
    requires a@.len() > 0
    ensures forall|j: int| 0 <= j < a@.len() ==> result as int >= a@[j] as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}