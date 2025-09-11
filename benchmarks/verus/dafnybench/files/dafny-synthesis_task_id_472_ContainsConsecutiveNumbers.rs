// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &[i32]) -> (result: bool)
    requires a.len() > 0
    ensures result <==> exists|i: int| #![trigger a.spec_index(i)] 
        0 <= i < (a.len() as int) - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}