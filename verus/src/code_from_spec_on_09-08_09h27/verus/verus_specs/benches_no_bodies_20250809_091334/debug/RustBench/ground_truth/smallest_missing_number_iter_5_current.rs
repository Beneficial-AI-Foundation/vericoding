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
        /* code modified by LLM (iteration 2): added explicit trigger annotation */
        forall|k: int| 0 <= k < v ==> exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == k,
{
    let mut expected = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added explicit trigger annotations to loop invariants */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            expected >= 0,
            forall|k: int| 0 <= k < expected ==> exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == k,
            forall|j: int| 0 <= j < i ==> s[j] < expected,
        decreases s.len() - i
    {
        if s[i] == expected {
            expected = expected + 1;
        } else if s[i] > expected {
            break;
        }
        i = i + 1;
    }
    
    expected
}

fn main() {}
}