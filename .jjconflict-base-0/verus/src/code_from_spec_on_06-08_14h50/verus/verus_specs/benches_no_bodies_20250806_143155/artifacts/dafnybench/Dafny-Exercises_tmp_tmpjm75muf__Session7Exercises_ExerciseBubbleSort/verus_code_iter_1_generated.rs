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
        while i < f - 1
            invariant
                c <= i <= f,
                a.len() == old(a).len(),
        {
            let mut j = c;
            while j < f - 1 - (i - c)
                invariant
                    c <= j <= f,
                    c <= i < f,
                    a.len() == old(a).len(),
            {
                if a[j] > a[j + 1] {
                    let temp = a[j];
                    a.set(j, a[j + 1]);
                    a.set(j + 1, temp);
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
        let mut n = f - c;
        
        while swapped && n > 1
            invariant
                1 <= n <= f - c + 1,
                a.len() == old(a).len(),
        {
            swapped = false;
            let mut i = c;
            while i < c + n - 1
                invariant
                    c <= i <= c + n,
                    a.len() == old(a).len(),
            {
                if a[i] > a[i + 1] {
                    let temp = a[i];
                    a.set(i, a[i + 1]);
                    a.set(i + 1, temp);
                    swapped = true;
                }
                i += 1;
            }
            n -= 1;
        }
    }
}

fn main() {}