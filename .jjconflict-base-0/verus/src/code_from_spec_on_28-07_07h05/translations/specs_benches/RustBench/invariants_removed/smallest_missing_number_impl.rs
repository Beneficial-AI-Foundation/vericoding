use vstd::prelude::*;

verus! {

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
{
    let mut candidate = 0i32;
    let mut i = 0usize;
    
    /* code modified by LLM (iteration 1): added trigger annotations to quantifiers to fix automatic trigger inference error */
    while i < s.len()
        invariant
            0 <= candidate,
            i <= s.len(),
            forall|k: int| #[trigger] s[k] 0 <= k < candidate ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
            i < s.len() ==> s[i as int] >= candidate,
            forall|j: int| #[trigger] s[j] 0 <= j < i ==> s[j] < candidate,
        decreases s.len() - i
    {
        if s[i] == candidate {
            candidate = candidate + 1;
        }
        i = i + 1;
    }
    
    candidate
}

fn main() {}
}