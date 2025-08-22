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
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall|k: int| 0 <= k < i ==> a[k] != e,
                /* code modified by LLM (iteration 1): added invariant to maintain existence of target element in remaining array portion */
                exists|j: int| i <= j < a.len() && a[j] == e,
            /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
            decreases a.len() - i
        {
            if a[i] == e {
                return i;
            }
            i += 1;
        }
        /* code modified by LLM (iteration 2): replaced unreachable!() with unreachable code that Verus can verify will never execute */
        0  // This line is unreachable due to the loop invariant
    }
}

fn main() {}