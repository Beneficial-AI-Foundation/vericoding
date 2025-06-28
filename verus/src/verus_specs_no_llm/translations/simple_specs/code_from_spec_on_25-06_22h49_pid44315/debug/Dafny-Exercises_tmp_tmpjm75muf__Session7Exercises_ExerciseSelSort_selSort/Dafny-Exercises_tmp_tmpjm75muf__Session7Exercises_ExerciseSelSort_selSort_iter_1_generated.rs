use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l as usize] <= a[k as usize]
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
    
    while i < f
        invariant
            c <= i <= f,
            a.len() == old(a).len(),
            // Already sorted portion
            sorted_seg(a, c as int, i as int),
            // Elements before sorted portion are <= elements in sorted portion
            forall|x: int, y: int| c <= x < i && i <= y < f ==> a[x as usize] <= a[y as usize],
            // Elements outside [c,f) unchanged
            forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
            forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
    {
        // Find minimum element in unsorted portion [i, f)
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < f
            invariant
                i <= min_idx < j <= f,
                // min_idx points to minimum element found so far
                forall|k: int| i <= k < j ==> a[min_idx] <= a[k as usize],
                a.len() == old(a).len(),
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        // Swap minimum element to position i
        if min_idx != i {
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
        }
        
        i += 1;
    }
}

}