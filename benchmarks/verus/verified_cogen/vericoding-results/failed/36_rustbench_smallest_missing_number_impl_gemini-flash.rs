// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added `decreases s.len() - i` to the loop to fix the verification error. */
{
    let mut i: int = 0;
    while (i as usize) < s.len()
        invariant
            0 <= i <= s.len() as int,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
        decreases s.len() - i
    {
        if s[i as usize] != i as i32 {
            return i as i32;
        }
        i = i + 1;
    }
    return i as i32;
}
// </vc-code>

}
fn main() {}