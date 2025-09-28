// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatch in next_candidate function by using i32 arithmetic */
spec fn contains_value(s: &[i32], val: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

spec fn all_smaller_present(s: &[i32], val: i32) -> bool {
    forall|k: i32| 0 <= k < val ==> contains_value(s, k)
}

spec fn next_candidate(s: &[i32], start: i32) -> i32 {
    if contains_value(s, start) {
        start + 1i32
    } else {
        start
    }
}
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
{
    /* code modified by LLM (iteration 5): Fixed implementation to correctly find smallest missing number */
    let mut candidate = 0i32;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            candidate >= 0,
            candidate <= i,
            forall|k: i32| 0 <= k < candidate ==> contains_value(s, k),
            !contains_value(s, candidate),
        decreases s.len() - i
    {
        if s[i] == candidate {
            candidate = candidate + 1i32;
        }
        i = i + 1;
    }
    
    candidate
}
// </vc-code>

}
fn main() {}