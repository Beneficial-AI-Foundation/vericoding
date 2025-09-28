// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)

    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,

    ensures
        odd_index < v.len(),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] % 2 != 1,
        decreases v.len() - i,
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i = i + 1;
    }

    proof {
        assert(forall|j: int| 0 <= j < v.len() ==> v@[j] % 2 != 1) by {
            // This is the loop invariant when the loop terminates
        };
        assert(exists|q: int| 0 <= q < v.len() && v@[q] % 2 == 1);
        assert(false);
    }
    // This part of the code is unreachable, so any return value is fine.
    // The compiler needs a return value to be syntactically correct.
    // The verifier proves this path is never taken.
    return 0;
}
// </vc-code>

}
fn main() {}