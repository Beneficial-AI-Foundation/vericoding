use vstd::prelude::*;

verus! {
    fn bubble_sort(a: &mut Vec<i32>)
        requires old(a).len() >= 0,
        ensures 
            // Array is sorted
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
            // Length is preserved
            a.len() == old(a).len(),
    {
        let n = a.len();
        let mut i: usize = 0;
        
        while i < n
            invariant
                i <= n,
                a.len() == n,
                // Elements from i onwards are in their final sorted positions
                forall|x: int, y: int| i <= x < y < a.len() ==> a[x] <= a[y],
                // Elements before i are <= all elements from i onwards
                forall|x: int, y: int| 0 <= x < i && i <= y < a.len() ==> a[x] <= a[y],
        {
            let mut j: usize = 0;
            
            while j < n - 1 - i
                invariant
                    i < n,
                    j <= n - 1 - i,
                    a.len() == n,
                    // Elements from (n-i) onwards are in their final sorted positions
                    forall|x: int, y: int| (n - i) <= x < y < a.len() ==> a[x] <= a[y],
                    // Elements before (n-i) are <= all elements from (n-i) onwards  
                    forall|x: int, y: int| 0 <= x < (n - i) && (n - i) <= y < a.len() ==> a[x] <= a[y],
                    // The largest element in range [0, j+1] is at position j+1 (if j+1 < n-i)
                    forall|k: int| 0 <= k <= j ==> a[k] <= a[j + 1],
            {
                if a[j] > a[j + 1] {
                    /* code modified by LLM (iteration 1): fixed borrowing issue by storing values in temporary variables before swap */
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
}

fn main() {}