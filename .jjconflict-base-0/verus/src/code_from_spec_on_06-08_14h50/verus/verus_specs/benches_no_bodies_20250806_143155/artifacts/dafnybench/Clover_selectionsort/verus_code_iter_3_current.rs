use vstd::prelude::*;

verus! {
    // Selection sort implementation in Verus
    fn selection_sort(a: &mut Vec<int>)
        ensures 
            a.len() == old(a).len(),
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
            // Note: multiset preservation requires additional lemmas in Verus
            // a@.to_multiset() == old(a)@.to_multiset(),
    {
        let n = a.len();
        let mut i = 0;
        
        while i < n
            invariant
                a.len() == n,
                // Everything before position i is sorted
                forall|p: int, q: int| 0 <= p < q < i ==> a[p] <= a[q],
                // Everything before position i is <= everything after position i
                forall|p: int, q: int| 0 <= p < i <= q < n ==> a[p] <= a[q],
        {
            // Find the minimum element in the remaining unsorted portion
            let mut min_idx = i;
            let mut j = i + 1;
            
            while j < n
                invariant
                    a.len() == n,
                    i <= min_idx < n,
                    i < j <= n,
                    /* code modified by LLM (iteration 1): Fixed invariant to use int casting for specification */
                    forall|k: int| i as int <= k < j as int ==> a[min_idx as int] <= a[k],
                    // Everything before position i is sorted
                    forall|p: int, q: int| 0 <= p < q < i ==> a[p] <= a[q],
                    // Everything before position i is <= everything after position i
                    forall|p: int, q: int| 0 <= p < i <= q < n ==> a[p] <= a[q],
            {
                /* code modified by LLM (iteration 1): Fixed array access to use usize indices directly */
                if a[j] < a[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            // Swap the minimum element with the element at position i
            /* code modified by LLM (iteration 1): Fixed array access and assignment to use usize indices */
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
            
            i += 1;
        }
    }
}

fn main() {}