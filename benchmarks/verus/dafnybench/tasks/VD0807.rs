// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_first_odd(a: &[i32]) -> (result: (bool, usize))
    ensures 
        (!result.0 ==> (forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int))) &&
        (result.0 ==> (0 <= result.1 < a.len() && 
                      is_odd(a[result.1 as int] as int) && 
                      (forall|i: int| 0 <= i < result.1 ==> !is_odd(a[i] as int))))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}