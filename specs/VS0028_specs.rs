// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn np_isclose(a: Vec<i8>, b: Vec<i8>, tol: i8) -> (result: Vec<bool>)
    requires 
        a.len() > 0,
        a.len() == b.len(),
        tol > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (-(tol as int) < (a[i] as int) - (b[i] as int) && (a[i] as int) - (b[i] as int) < (tol as int)),
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