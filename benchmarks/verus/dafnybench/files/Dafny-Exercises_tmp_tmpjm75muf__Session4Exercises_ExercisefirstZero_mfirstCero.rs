// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mfirst_cero(v: &Vec<i8>) -> (i: usize)
    ensures
        i <= v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] as i8 != 0,
        i != v.len() ==> v@[i as int] as i8 == 0,
{
    assume(false);
    0
}
// </vc-spec>
// <vc-code>
// </vc-code>

}
fn main() {}