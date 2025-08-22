use vstd::prelude::*;

verus! {
    fn barrier(v: &[int], p: usize) -> (b: bool)
        requires 
            v.len() > 0,
            p < v.len(),
        ensures 
            /* code modified by LLM (iteration 1): use @ operator for sequence access and proper int types */
            b == (forall|k: int, l: int| 0 <= k <= p && p < l < v.len() ==> v@[k] < v@[l])
    {
        let mut i = 0;
        while i <= p
            invariant
                0 <= i <= p + 1,
                /* code modified by LLM (iteration 1): use @ operator for sequence access in invariants */
                forall|k: int, l: int| 0 <= k < i && p < l < v.len() ==> v@[k] < v@[l]
            /* code modified by LLM (iteration 2): add decreases clause for outer loop */
            decreases p + 1 - i
        {
            let mut j = p + 1;
            while j < v.len()
                invariant
                    p + 1 <= j <= v.len(),
                    /* code modified by LLM (iteration 1): use @ operator and proper int indexing */
                    forall|k: int, l: int| 0 <= k < i && p < l < v.len() ==> v@[k] < v@[l],
                    forall|l: int| p < l < j ==> v@[i as int] < v@[l]
                /* code modified by LLM (iteration 2): add decreases clause for inner loop */
                decreases v.len() - j
            {
                if v[i] >= v[j] {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        true
    }
}

fn main() {}