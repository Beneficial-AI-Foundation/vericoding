use vstd::prelude::*;

verus! {
    fn linear_search(a: &[int], e: int) -> (n: usize)
        requires 
            exists|i: int| 0 <= i < a.len() && a[i] == e,
        ensures 
            0 <= n < a.len(),
            a[n as int] == e,
            forall|k: int| 0 <= k < n ==> a[k] != e,
    {
        let mut i: usize = 0;
        
        while i < a.len()
            invariant
                i <= a.len(),
                forall|k: int| 0 <= k < i ==> a[k] != e,
                exists|j: int| i <= j < a.len() && a[j] == e,
        {
            /* code modified by LLM (iteration 1): fixed indexing to use ghost variable for int cast */
            let ghost idx: int = i as int;
            if a[idx] == e {
                return i;
            }
            i = i + 1;
        }
        
        // This point should never be reached due to the precondition
        unreachable!()
    }
}

fn main() {}