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
    
    while i < n
        invariant
            i <= n,
            a.len() == n,
            n >= 1,
            forall|k: int| 0 <= k < a.len() ==> a[k as usize].len() == 2,
            // Permutation is maintained
            forall|k: int| 0 <= k < a.len() ==> 
                exists|j: int| 0 <= j < old(a).len() && 
                a[k as usize][0] == old(a)[j as usize][0] && 
                a[k as usize][1] == old(a)[j as usize][1],
            // After i iterations, the last i elements are sorted and in final positions
            forall|k1: int, k2: int| (n - i) <= k1 <= k2 < n ==> 
                a[k1 as usize][1] <= a[k2 as usize][1],
            // Elements before the sorted suffix are <= elements in the sorted suffix
            forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> 
                a[k1 as usize][1] <= a[k2 as usize][1],
    {
        if i == n {
            break;
        }
        
        // Bubble the largest element to the end
        let mut j: usize = 0;
        
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                a.len() == n,
                n >= 1,
                forall|k: int| 0 <= k < a.len() ==> a[k as usize].len() == 2,
                // Permutation is maintained through swaps
                forall|k: int| 0 <= k < a.len() ==> 
                    exists|m: int| 0 <= m < old(a).len() && 
                    a[k as usize][0] == old(a)[m as usize][0] && 
                    a[k as usize][1] == old(a)[m as usize][1],
                // After i iterations, the last i elements remain sorted
                forall|k1: int, k2: int| (n - i) <= k1 <= k2 < n ==> 
                    a[k1 as usize][1] <= a[k2 as usize][1],
                // Elements before the sorted suffix are <= elements in the sorted suffix
                forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> 
                    a[k1 as usize][1] <= a[k2 as usize][1],
                // The maximum element in 0..j is at position j
                forall|k: int| 0 <= k <= j ==> 
                    a[k as usize][1] <= a[j as usize][1],
        {
            if a[j][1] > a[j + 1][1] {
                // Swap elements
                let temp0 = a[j][0];
                let temp1 = a[j][1];
                
                a[j][0] = a[j + 1][0];
                a[j][1] = a[j + 1][1];
                a[j + 1][0] = temp0;
                a[j + 1][1] = temp1;
            }
            
            j += 1;
        }
        
        // After inner loop, the maximum element is bubbled to position n-1-i
        assert(forall|k: int| 0 <= k < (n - i) ==> 
            a[k as usize][1] <= a[(n - 1 - i) as usize][1]);
        
        i += 1;
    }
    
    // After the outer loop, the array is fully sorted
    assert(forall|k1: int, k2: int| 0 <= k1 <= k2 < a.len() ==> 
        a[k1 as usize][1] <= a[k2 as usize][1]);
}

}