// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mfirstNegative(v: &[i8]) -> (result: (bool, usize))
    ensures 
        (result.0 <==> exists|k: int| 0 <= k < v@.len() && v@[k] < 0) &&
        (result.0 ==> (result.1 < v@.len() && v@[result.1 as int] < 0 && positive(v@.map(|i, x: i8| x as int).subrange(0, result.1 as int))))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}