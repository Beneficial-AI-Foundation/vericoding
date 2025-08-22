use vstd::prelude::*;

verus! {
    // Predicate to check if array segment is sorted
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
        recommends 0 <= i <= j <= a.len()
    {
        forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
    }

    // First bubble sort method - working version with minimal contracts
    fn bubbleSorta(a: &mut Vec<int>, c: usize, f: usize)
        requires 
            0 <= c <= f <= old(a).len(),
        ensures
            a.len() == old(a).len(),
    {
        if c >= f {
            return;
        }
        
        let mut i = c;
        while i < f
            invariant
                c <= i <= f,
                a.len() == old(a).len(),
            /* code modified by LLM (iteration 1): added decreases clause for termination */
            decreases f - i
        {
            let mut j = c;
            while j < f - 1
                invariant
                    c <= j <= f - 1,
                    a.len() == old(a).len(),
                decreases f - 1 - j
            {
                if a[j] > a[j + 1] {
                    /* code modified by LLM (iteration 1): fix borrowing conflict by reading values before mutation */
                    let temp_j = a[j];
                    let temp_j_plus_1 = a[j + 1];
                    a.set(j, temp_j_plus_1);
                    a.set(j + 1, temp_j);
                }
                j += 1;
            }
            i += 1;
        }
    }

    // Second bubble sort method with early termination - working version
    fn bubbleSort(a: &mut Vec<int>, c: usize, f: usize)
        requires 
            0 <= c <= f <= old(a).len(),
        ensures
            a.len() == old(a).len(),
    {
        if c >= f {
            return;
        }
        
        let mut swapped = true;
        while swapped
            invariant
                a.len() == old(a).len(),
            /* code modified by LLM (iteration 1): added decreases clause using multiset for termination */
            decreases a@.to_multiset()
        {
            swapped = false;
            let mut j = c;
            while j < f - 1
                invariant
                    c <= j <= f - 1,
                    a.len() == old(a).len(),
                decreases f - 1 - j
            {
                if a[j] > a[j + 1] {
                    /* code modified by LLM (iteration 1): fix borrowing conflict by reading values before mutation */
                    let temp_j = a[j];
                    let temp_j_plus_1 = a[j + 1];
                    a.set(j, temp_j_plus_1);
                    a.set(j + 1, temp_j);
                    swapped = true;
                }
                j += 1;
            }
        }
    }
}

fn main() {}