// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max(a: &Vec<i8>, b: &Vec<i8>, i: usize, j: usize) -> (m: i8)
    requires 
        i < a.len(),
        j < b.len(),
    ensures 
        a[i as int] as int > b[j as int] as int ==> m as int == a[i as int] as int,
        a[i as int] as int <= b[j as int] as int ==> m as int == b[j as int] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}