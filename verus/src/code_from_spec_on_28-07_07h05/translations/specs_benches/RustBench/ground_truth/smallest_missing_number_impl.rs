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
        /* code modified by LLM (iteration 3): added explicit trigger annotation to fix trigger inference error */
        forall|k: int| #[trigger] (0 <= k < v) ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
{
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 3): added explicit trigger annotation to fix trigger inference error */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| #[trigger] (0 <= k < i) ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
        decreases s.len() - i
    {
        if s[i] > i as i32 {
            return i as i32;
        }
        i += 1;
    }
    
    s.len() as i32
}

fn main() {}
}