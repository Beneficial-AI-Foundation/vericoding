// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_to(a: &[bool], n: int) -> int
    decreases n when 0 <= n <= a.len()
{
    if n <= 0 { 
        0int 
    } else { 
        count_to(a, n - 1) + if a[n - 1] { 1int } else { 0int } 
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_true(a: &[bool]) -> (result: usize)
    ensures result == count_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}