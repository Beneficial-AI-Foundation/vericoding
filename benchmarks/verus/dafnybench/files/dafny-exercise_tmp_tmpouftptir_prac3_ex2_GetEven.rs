// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_even(s: &mut Vec<u8>)
    ensures 
        s@.len() == old(s)@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if old(s)@[i] as nat % 2 == 1 {
                s@[i] as nat == old(s)@[i] as nat + 1
            } else {
                s@[i] as nat == old(s)@[i] as nat
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