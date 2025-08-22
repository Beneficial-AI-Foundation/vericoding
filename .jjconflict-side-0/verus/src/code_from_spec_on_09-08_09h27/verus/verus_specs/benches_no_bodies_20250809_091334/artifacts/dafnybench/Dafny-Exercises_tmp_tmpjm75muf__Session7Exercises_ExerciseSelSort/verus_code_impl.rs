use vstd::prelude::*;

verus! {
    // Predicate to check if a segment of array is sorted
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool 
        recommends 0 <= i <= j <= a.len()
    {
        forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
    }

    fn sel_sort(a: &mut Vec<int>, c: usize, f: usize)
        requires 
            c <= f,
            f <= old(a).len(),
        ensures 
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, f as int),
    {
        let mut i = c;
        while i < f
            invariant
                c <= i <= f,
                f <= a.len(),
                a.len() == old(a).len(),
                sorted_seg(a@, c as int, i as int),
                forall|k: int, l: int| c <= k < i && i <= l < f ==> a@[k] <= a@[l],
            /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
            decreases f - i
        {
            let mut min_idx = i;
            let mut j = i + 1;
            
            while j < f
                invariant
                    i < f,
                    i <= min_idx < j <= f,
                    f <= a.len(),
                    a.len() == old(a).len(),
                    forall|k: int| i <= k < j ==> a@[min_idx as int] <= a@[k],
                /* code modified by LLM (iteration 1): Added decreases clause for inner loop */
                decreases f - j
            {
                if a[j] < a[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            /* code modified by LLM (iteration 1): Fixed borrowing issue by storing values before mutable operations */
            // Swap elements at positions i and min_idx
            let temp = a[i];
            let min_val = a[min_idx];
            a.set(i, min_val);
            a.set(min_idx, temp);
            
            i += 1;
        }
    }
}

fn main() {}