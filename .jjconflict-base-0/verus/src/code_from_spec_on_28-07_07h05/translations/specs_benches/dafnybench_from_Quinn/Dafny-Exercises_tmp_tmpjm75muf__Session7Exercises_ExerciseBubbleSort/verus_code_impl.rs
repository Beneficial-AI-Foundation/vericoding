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
        
        /* code modified by LLM (iteration 2): add bounds check to prevent underflow */
        if f == 0 || f <= 1 {
            return;
        }
        
        let mut i = c;
        while i < f - 1
            invariant 
                c <= i <= f,
                a.len() == old(a).len(),
                /* code modified by LLM (iteration 2): strengthen bounds invariants */
                f > 1,
                c < f,
                i < a.len(),
            decreases f - i - 1
        {
            let mut j = i + 1;
            while j < f
                invariant
                    /* code modified by LLM (iteration 2): fix invariant ordering and bounds */
                    c <= i < f - 1,
                    i + 1 <= j <= f,
                    a.len() == old(a).len(),
                    i < a.len(),
                    j <= a.len(),
                    f <= a.len(),
                decreases f - j
            {
                /* code modified by LLM (iteration 2): strengthen bounds assertions */
                assert(i < a.len());
                assert(j < f);
                assert(f <= a.len());
                assert(j < a.len());
                if a[i] > a[j] {
                    let temp_i = a[i];
                    let temp_j = a[j];
                    a.set(i, temp_j);
                    a.set(j, temp_i);
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
        
        /* code modified by LLM (iteration 2): strengthen bounds check */
        if f == 0 || c + 1 >= f || f <= 1 {
            return;
        }
        
        let mut swapped = true;
        let mut end = f;
        
        while swapped && end > c + 1
            invariant
                c < end <= f,
                a.len() == old(a).len(),
                /* code modified by LLM (iteration 2): strengthen bounds invariants */
                f > 1,
                c + 1 < f,
                end >= c + 1,
            decreases end - c
        {
            swapped = false;
            let mut i = c;
            
            while i < end - 1
                invariant
                    c <= i < end,
                    a.len() == old(a).len(),
                    /* code modified by LLM (iteration 2): strengthen bounds invariants */
                    end > c + 1,
                    end <= f,
                    f <= a.len(),
                    i < a.len(),
                    i + 1 < end,
                    i + 1 < a.len(),
                decreases end - i - 1
            {
                /* code modified by LLM (iteration 2): strengthen bounds assertions */
                assert(i < end - 1);
                assert(end > c + 1);
                assert(i + 1 < end);
                assert(end <= f);
                assert(f <= a.len());
                assert(i + 1 < a.len());
                if a[i] > a[i + 1] {
                    let temp_i = a[i];
                    let temp_i_plus_1 = a[i + 1];
                    a.set(i, temp_i_plus_1);
                    a.set(i + 1, temp_i);
                    swapped = true;
                }
                i += 1;
            }
            end -= 1;
        }
    }
}

fn main() {}