use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
{
    let mut candidate = 0;
    loop
        invariant
            0 <= candidate,
            /* code modified by LLM (iteration 1): added trigger annotation to fix quantifier inference error */
            forall|k: int| 0 <= k < candidate ==> exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == k,
        decreases s.len() - candidate
    {
        let mut found = false;
        let mut i = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
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
        
        proof {
            assert(candidate <= s.len());
        }
    }
}

fn main() {}
}