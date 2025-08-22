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
            if a[i] == e {
                return i;
            }
            i = i + 1;
        }
        
        /* code modified by LLM (iteration 1): remove unreachable!() and add proof that this case is impossible */
        proof {
            // At this point i == a.len(), but our invariant guarantees there exists j such that
            // i <= j < a.len() and a[j] == e. Since i == a.len(), there's no such j.
            // This contradicts our invariant, so this point is unreachable.
            assert(i == a.len());
            assert(exists|j: int| i <= j < a.len() && a[j] == e);
            assert(false); // contradiction
        }
        0 // This line will never execute due to the assertion above
    }
}

fn main() {}