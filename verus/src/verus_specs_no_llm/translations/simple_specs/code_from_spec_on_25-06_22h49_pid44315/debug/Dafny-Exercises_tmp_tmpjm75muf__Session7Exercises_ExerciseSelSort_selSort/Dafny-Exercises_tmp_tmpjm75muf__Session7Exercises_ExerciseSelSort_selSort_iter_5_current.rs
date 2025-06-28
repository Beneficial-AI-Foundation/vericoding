use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l < k < j ==> a[l as usize] <= a[k as usize]
}

fn sel_sort(a: &mut Vec<i32>, c: usize, f: usize)
    requires 
        0 <= c <= f <= a.len(),
    ensures
        sorted_seg(a, c as int, f as int),
        a.len() == old(a).len(),
        // Elements outside [c,f) are unchanged
        forall|i: int| 0 <= i < c ==> a[i as usize] == old(a)[i as usize],
        forall|i: int| f <= i < a.len() ==> a[i as usize] == old(a)[i as usize],
{
    let mut i = c;
    let ghost orig_a = *a;
    
    while i < f
        invariant
            c <= i <= f,
            a.len() == orig_a.len(),
            // Already sorted portion
            sorted_seg(a, c as int, i as int),
            // Elements in sorted portion are <= elements in unsorted portion
            forall|x: int, y: int| c <= x < i && i <= y < f ==> a[x as usize] <= a[y as usize],
            // Elements outside [c,f) unchanged
            forall|k: int| 0 <= k < c ==> a[k as usize] == orig_a[k as usize],
            forall|k: int| f <= k < a.len() ==> a[k as usize] == orig_a[k as usize],
    {
        // Find minimum element in unsorted portion [i, f)
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < f
            invariant
                i < f,
                i <= min_idx < j <= f,
                min_idx < a.len(),
                j <= a.len(),
                // min_idx points to minimum element found so far in [i, j)
                forall|k: int| (i as int) <= k < (j as int) ==> a[min_idx] <= a[k as usize],
                // Array length unchanged
                a.len() == orig_a.len(),
                // Sorted portion unchanged
                sorted_seg(a, c as int, i as int),
                // Elements in sorted portion <= elements in unsorted portion
                forall|x: int, y: int| c <= x < i && i <= y < f ==> a[x as usize] <= a[y as usize],
                // Elements outside [c,f) unchanged  
                forall|k: int| 0 <= k < c ==> a[k as usize] == orig_a[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == orig_a[k as usize],
        {
            assert(j < a.len());
            assert(min_idx < a.len());
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        // After inner loop, min_idx points to minimum in [i, f)
        assert(forall|k: int| (i as int) <= k < (f as int) ==> a[min_idx] <= a[k as usize]);
        
        // Swap minimum element to position i
        if min_idx != i {
            assert(i < a.len());
            assert(min_idx < a.len());
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
        }
        
        // Prove that the element at position i is <= all elements in [i+1, f)
        assert(forall|k: int| (i as int) < k < (f as int) ==> a[i] <= a[k as usize]);
        
        // Prove sorted_seg property for extended range
        assert(forall|l: int, k: int| (c as int) <= l < k < ((i + 1) as int) ==> a[l as usize] <= a[k as usize]) by {
            // The proof follows from the loop invariant and the fact that we placed the minimum at position i
        };
        
        // Prove that elements in new sorted portion are <= elements in remaining unsorted portion
        assert(forall|x: int, y: int| c <= x < (i + 1) && (i + 1) <= y < f ==> a[x as usize] <= a[y as usize]) by {
            // This follows from the fact that a[i] is the minimum of [i, f) and previous invariant
        };
        
        i += 1;
    }
}

}