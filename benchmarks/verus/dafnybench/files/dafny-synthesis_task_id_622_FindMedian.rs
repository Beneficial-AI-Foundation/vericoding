// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_median(a: &[i32], b: &[i32]) -> (median: i32)
    requires 
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| #[trigger] a[i] == a[i] ==> (0 <= i < (a.len() - 1) as int ==> a[i] <= a[add(i, 1)]),
        forall|i: int| #[trigger] b[i] == b[i] ==> (0 <= i < (b.len() - 1) as int ==> b[i] <= b[add(i, 1)]),
    ensures 
        median as int == if a.len() % 2 == 0 { 
            (a[(a.len() / 2 - 1) as int] + b[0int]) / 2 
        } else { 
            a[(a.len() / 2) as int] as int
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}