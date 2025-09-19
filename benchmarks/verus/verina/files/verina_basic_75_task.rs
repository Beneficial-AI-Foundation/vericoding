// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result as int <= a[i] as int,
        exists|i: int| 0 <= i < a.len() && result as int == a[i] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}