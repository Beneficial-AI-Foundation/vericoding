use vstd::prelude::*;

verus! {
    fn bubble_sort(a: &mut Vec<i32>)
        requires old(a).len() >= 0,
        ensures 
            // Array is sorted
            forall|i: int, j: int| 0 <= i < j < a.len() ==> a@[i] <= a@[j],
            // Length is preserved
            a.len() == old(a).len(),
    {
        let n = a.len();
        let mut i = 0;
        
        while i < n
            invariant
                0 <= i <= n,
                a.len() == n,
                // Elements from i to n-1 are in their final sorted positions
                forall|k: int, l: int| i <= k < l < n ==> a@[k] <= a@[l],
                // Elements from 0 to i-1 are <= all elements from i to n-1
                forall|k: int, l: int| 0 <= k < i && i <= l < n ==> a@[k] <= a@[l],
        {
            let mut j = 0;
            
            while j < n - 1 - i
                invariant
                    0 <= i < n,
                    0 <= j <= n - 1 - i,
                    a.len() == n,
                    // Elements from i+1 to n-1 are in their final sorted positions
                    forall|k: int, l: int| i + 1 <= k < l < n ==> a@[k] <= a@[l],
                    // Elements from 0 to i-1 are <= all elements from i+1 to n-1
                    forall|k: int, l: int| 0 <= k < i && i + 1 <= l < n ==> a@[k] <= a@[l],
                    // The maximum element in range [0, n-1-i] is at or before position j
                    forall|k: int| j < k < n - i ==> a@[j] <= a@[k],
            {
                /* code modified by LLM (iteration 1): Fixed vector indexing to use @ operator and proper bounds checking */
                if a@[j as int] > a@[j as int + 1] {
                    let temp = a@[j as int];
                    a.set(j, a@[j as int + 1]);
                    a.set(j + 1, temp);
                }
                j = j + 1;
            }
            i = i + 1;
        }
    }
}

fn main() {}