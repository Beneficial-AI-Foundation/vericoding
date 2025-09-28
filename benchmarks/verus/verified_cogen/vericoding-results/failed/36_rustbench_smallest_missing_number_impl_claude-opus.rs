// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains(s: &[i32], v: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == v
}

proof fn lemma_sorted_contains(s: &[i32], v: i32, idx: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        0 <= idx < s.len(),
        s[idx] == v,
    ensures
        contains(s, v),
{
    assert(0 <= idx < s.len() && s[idx] == v);
}

/* helper modified by LLM (iteration 5): fixed type mismatch in lemma */
proof fn lemma_missing_found(s: &[i32], k: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        0 <= k,
        forall|i: int| 0 <= i < s.len() ==> s[i] != k,
        forall|j: int| 0 <= j < k ==> #[trigger] s[j] == j || exists|i: int| 0 <= i < s.len() && s[i] == j,
    ensures
        forall|j: int| 0 <= j < k && s[j] != k ==> exists|i: int| 0 <= i < s.len() && s[i] == j,
{
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
    /* code modified by LLM (iteration 5): fixed type conversion for contains function calls */
    let mut candidate: i32 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= candidate,
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < candidate ==> contains(s, j as i32),
            forall|j: int| 0 <= j < i ==> s[j] >= candidate,
        decreases s.len() - i,
    {
        if s[i] == candidate {
            candidate = candidate + 1;
            i = 0;
        } else {
            i = i + 1;
        }
    }
    
    proof {
        assert(forall|j: int| 0 <= j < s.len() ==> s[j] != candidate);
        assert(forall|j: int| 0 <= j < candidate ==> contains(s, j as i32));
    }
    
    candidate
}
// </vc-code>

}
fn main() {}