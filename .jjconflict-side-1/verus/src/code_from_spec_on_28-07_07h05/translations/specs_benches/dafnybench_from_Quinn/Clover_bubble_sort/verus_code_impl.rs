//IMPL bubble_sort
use vstd::prelude::*;

verus! {
    /* code modified by LLM (iteration 4): Fixed trigger annotation syntax */
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
                a.len() == n,
                i <= n,
                // Elements 0..i are in their final sorted positions
                forall|x: int, y: int| 0 <= x < y < i ==> a[x] <= a[y],
                // Elements in 0..i are <= all elements in i..n
                forall|x: int, y: int| 0 <= x < i && i <= y < n ==> a[x] <= a[y],
            decreases n - i
        {
            let mut j: usize = 0;
            
            while j < n - 1 - i
                invariant
                    a.len() == n,
                    i < n,
                    j <= n - 1 - i,
                    // Elements 0..i remain in sorted order
                    forall|x: int, y: int| 0 <= x < y < i ==> a[x] <= a[y],
                    // Elements in 0..i are <= all elements in i..n
                    forall|x: int, y: int| 0 <= x < i && i <= y < n ==> a[x] <= a[y],
                    // The largest element in i+j..n is now in position n-1-i or later
                    /* code modified by LLM (iteration 4): Fixed trigger to use array access pattern instead of value */
                    forall|k: int| (i + j) <= k < n - 1 - i ==> a[k] <= a[n - 1 - i],
                decreases (n - 1 - i) - j
            {
                let a_j = a[j];
                let a_j_plus_1 = a[j + 1];
                if a_j > a_j_plus_1 {
                    a.set(j, a_j_plus_1);
                    a.set(j + 1, a_j);
                }
                j += 1;
            }
            i += 1;
        }
    }
}

fn main() {}