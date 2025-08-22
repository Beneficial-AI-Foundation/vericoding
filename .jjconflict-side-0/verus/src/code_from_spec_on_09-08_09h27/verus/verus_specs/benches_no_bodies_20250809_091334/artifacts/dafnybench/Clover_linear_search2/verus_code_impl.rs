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
        /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall|k: int| 0 <= k < i ==> a[k] != e,
                exists|j: int| i <= j < a.len() && a[j] == e,
            decreases a.len() - i
        {
            if a[i] == e {
                return i;
            }
            i += 1;
        }
        /* code modified by LLM (iteration 1): replaced unreachable!() with proof block and return 0 since this case should never be reached due to precondition */
        proof {
            // At this point i == a.len(), but we know from precondition that e exists in a
            // and from loop invariant that e exists in range [i, a.len())
            // Since i == a.len(), the range [i, a.len()) is empty, which is a contradiction
            assert(false);
        }
        0 // This line should never be reached
    }
}

fn main() {}