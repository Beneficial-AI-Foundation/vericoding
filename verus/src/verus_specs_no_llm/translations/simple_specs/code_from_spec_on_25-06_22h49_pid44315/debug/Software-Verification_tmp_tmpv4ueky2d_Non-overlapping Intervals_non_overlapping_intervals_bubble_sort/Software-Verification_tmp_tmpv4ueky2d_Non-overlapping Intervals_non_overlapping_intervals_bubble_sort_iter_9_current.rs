use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: &[Vec<int>], l: int, u: int) -> bool {
    forall|i: int, j: int| l <= i <= j <= u && 0 <= i < a.len() && 0 <= j < a.len() ==> 
        a[i as usize][1] <= a[j as usize][1]
}

spec fn multiset_equiv(a: &[Vec<int>], b: &[Vec<int>]) -> bool {
    a.len() == b.len() &&
    forall|i: int| 0 <= i < a.len() ==> 
        exists|j: int| 0 <= j < b.len() && 
        a[i as usize][0] == b[j as usize][0] && 
        a[i as usize][1] == b[j as usize][1]
}

// Helper spec function to check if an element is the minimum in a range
spec fn is_min_in_range(a: &[Vec<int>], pos: int, start: int, end: int) -> bool {
    start <= pos <= end < a.len() &&
    forall|k: int| start <= k <= end ==> a[pos as usize][1] <= a[k as usize][1]
}

// Bubble Sort
fn bubble_sort(a: &mut Vec<Vec<int>>)
    requires 
        old(a).len() >= 1,
        forall|i: int| 0 <= i < old(a).len() ==> old(a)[i as usize].len() == 2,
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i as usize].len() == 2,
        sorted(a, 0, (a.len() - 1) as int),
        // Permutation property - same multiset of elements
        forall|i: int| 0 <= i < a.len() ==> 
            exists|j: int| 0 <= j < old(a).len() && 
            a[i as usize][0] == old(a)[j as usize][0] && 
            a[i as usize][1] == old(a)[j as usize][1],
{
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n - 1
        invariant
            i <= n - 1,
            a.len() == n,
            n >= 1,
            forall|k: int| 0 <= k < a.len() ==> a[k as usize].len() == 2,
            // Elements 0..i are in their final sorted positions
            forall|k1: int, k2: int| 0 <= k1 <= k2 < i ==> 
                a[k1 as usize][1] <= a[k2 as usize][1],
            // Elements 0..i are <= all elements i..n  
            forall|k1: int, k2: int| 0 <= k1 < i && (i as int) <= k2 < a.len() ==> 
                a[k1 as usize][1] <= a[k2 as usize][1],
            // Permutation is maintained
            forall|k: int| 0 <= k < a.len() ==> 
                exists|j: int| 0 <= j < old(a).len() && 
                a[k as usize][0] == old(a)[j as usize][0] && 
                a[k as usize][1] == old(a)[j as usize][1],
    {
        // Bubble the minimum element from range i..n-1 to position i
        let mut j: usize = n - 1;
        
        while j > i
            invariant
                i < j < n,
                a.len() == n,
                n >= 1,
                forall|k: int| 0 <= k < a.len() ==> a[k as usize].len() == 2,
                // Elements 0..i remain in their final sorted positions
                forall|k1: int, k2: int| 0 <= k1 <= k2 < i ==> 
                    a[k1 as usize][1] <= a[k2 as usize][1],
                // Elements 0..i are <= elements i..n
                forall|k1: int, k2: int| 0 <= k1 < i && (i as int) <= k2 < a.len() ==> 
                    a[k1 as usize][1] <= a[k2 as usize][1],
                // Permutation is maintained through swaps
                forall|k: int| 0 <= k < a.len() ==> 
                    exists|m: int| 0 <= m < old(a).len() && 
                    a[k as usize][0] == old(a)[m as usize][0] && 
                    a[k as usize][1] == old(a)[m as usize][1],
                // Elements at positions i..j-1 have been processed
                forall|k: int| (i as int) <= k < (j as int) ==> 
                    a[k as usize][1] <= a[j as usize][1],
        {
            if a[j - 1][1] > a[j][1] {
                // Swap elements to bubble smaller element towards the front
                let temp0 = a[j - 1][0];
                let temp1 = a[j - 1][1];
                
                a[j - 1][0] = a[j][0];
                a[j - 1][1] = a[j][1];
                a[j][0] = temp0;
                a[j][1] = temp1;
            }
            
            j -= 1;
        }
        
        // After inner loop, the minimum element from range i..n-1 is now at position i
        assert(forall|k: int| (i as int) < k < a.len() ==> 
            a[i as usize][1] <= a[k as usize][1]);
        
        i += 1;
    }
    
    // After the outer loop, the array is fully sorted
    assert(forall|k1: int, k2: int| 0 <= k1 <= k2 < a.len() ==> 
        a[k1 as usize][1] <= a[k2 as usize][1]);
}

}