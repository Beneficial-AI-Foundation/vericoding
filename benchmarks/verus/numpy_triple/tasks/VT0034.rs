// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_int(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn vander(x: Vec<i8>, m: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x@.len() > 0,
        m > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == m,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < m ==> 
            result@[i]@[j] as int == pow_int(x@[i] as int, (m - 1 - j) as nat),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}