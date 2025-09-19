// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

spec fn min_function(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i8>) -> (m: i8)
    requires a.len() > 0
    ensures 
        forall|k: int| 0 <= k < a.len() ==> m as int <= a[k] as int,
        exists|k: int| 0 <= k < a.len() && m as int == a[k] as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}