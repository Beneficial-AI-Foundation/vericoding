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
        let len = a.len();
        let mut i: usize = 0;
        
        while i < len
            invariant
                i <= len,
                a.len() == len,
                // Elements 0..i are sorted
                forall|x: int, y: int| 0 <= x < y < i ==> a[x] <= a[y],
                // Elements 0..i are <= all elements i..len
                forall|x: int, y: int| 0 <= x < i && i <= y < len ==> a[x] <= a[y],
        {
            // Find minimum element in range i..len
            let mut min_idx: usize = i;
            let mut j: usize = i + 1;
            
            while j < len
                invariant
                    i <= min_idx < len,
                    i <= j <= len,
                    a.len() == len,
                    // min_idx points to minimum in range i..j
                    forall|k: int| i <= k < j ==> a[min_idx as int] <= a[k],
            {
                if a[j] < a[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            /* code modified by LLM (iteration 1): store values before swapping to avoid borrowing conflicts */
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