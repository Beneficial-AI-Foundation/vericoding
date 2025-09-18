// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variables for int casting and proper sequence access */
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != 'z' && s@[j] != 'Z',
    {
        let ghost ghost_i: int = i as int;
        proof {
            assert(0 <= ghost_i < s@.len());
        }
        if s@[ghost_i] == 'z' || s@[ghost_i] == 'Z' {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}