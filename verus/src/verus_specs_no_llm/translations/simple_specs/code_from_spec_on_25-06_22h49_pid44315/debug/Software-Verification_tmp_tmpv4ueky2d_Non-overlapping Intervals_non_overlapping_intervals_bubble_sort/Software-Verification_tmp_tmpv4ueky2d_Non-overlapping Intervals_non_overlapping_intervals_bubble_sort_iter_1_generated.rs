use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: &[Vec<int>], l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i as usize][1] <= a[j as usize][1]
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
            forall|k: int| 0 <= k < a.len() ==> a[k as usize].len() == 2,
            // Elements 0..i are in their final sorted positions
            forall|k1: int, k2: int| 0 <= k1 < i && i <= k2 < a.len() ==> 
                a[k1 as usize][1] <= a[k2 as usize][1],
            // Elements 0..i are sorted among themselves
            forall|k1: int, k2: int| 0 <= k1 <= k2 < i ==> 
                a[k1 as usize][1] <= a[k2 as usize][1],
    {
        let mut j: usize = n - 1;
        
        while j > i
            invariant
                i < n,
                i < j,
                j < n,
                a.len() == n,
                forall|k: int| 0 <= k < a.len() ==> a[k as usize].len() == 2,
                // The smallest element in range i..n has bubbled to position i or will bubble there
                forall|k: int| i < k <= j ==> a[i as usize][1] <= a[k as usize][1],
                forall|k1: int, k2: int| 0 <= k1 < i && i <= k2 < a.len() ==> 
                    a[k1 as usize][1] <= a[k2 as usize][1],
                forall|k1: int, k2: int| 0 <= k1 <= k2 < i ==> 
                    a[k1 as usize][1] <= a[k2 as usize][1],
        {
            if a[j - 1][1] > a[j][1] {
                // Swap rows
                let temp0 = a[j - 1][0];
                let temp1 = a[j - 1][1];
                a[j - 1][0] = a[j][0];
                a[j - 1][1] = a[j][1];
                a[j][0] = temp0;
                a[j][1] = temp1;
            }
            j -= 1;
        }
        i += 1;
    }
}

}