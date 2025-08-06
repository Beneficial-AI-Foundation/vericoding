use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
{
    let mut candidate: i32 = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    loop
        invariant
            0 <= candidate,
            /* code modified by LLM (iteration 2): added explicit trigger annotation for quantifier */
            forall|k: int| 0 <= k < candidate ==> exists|j: int| #[trigger] (0 <= j < s.len() && s[j] == k),
        decreases s.len() - candidate
    {
        let mut found = false;
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 2): added decreases clause for inner while loop */
        while i < s.len()
            invariant
                i <= s.len(),
                found ==> exists|j: int| 0 <= j < s.len() && s[j] == candidate,
                !found ==> forall|j: int| 0 <= j < i ==> s[j] != candidate,
            decreases s.len() - i
        {
            if s[i] == candidate {
                found = true;
                break;
            }
            i += 1;
        }
        
        if !found {
            return candidate;
        }
        
        candidate += 1;
    }
}

fn main() {}
}