// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_even(s: &mut Vec<nat>)
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> {
            if old(s)[i] % 2 == 1 {
                s[i] == old(s)[i] + 1
            } else {
                s[i] == old(s)[i]
            }
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