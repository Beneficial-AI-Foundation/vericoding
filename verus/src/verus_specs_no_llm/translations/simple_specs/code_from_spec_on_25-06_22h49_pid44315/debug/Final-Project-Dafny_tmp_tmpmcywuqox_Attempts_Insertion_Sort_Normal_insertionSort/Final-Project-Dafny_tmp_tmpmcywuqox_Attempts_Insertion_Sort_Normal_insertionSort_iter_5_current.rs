use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sortedA(a: Vec<int>, i: int) -> bool
    requires 0 <= i <= a.len()
{
    forall|k: int| 0 <= k < i - 1 ==> a.spec_index(k) <= a.spec_index(k + 1)
}

fn lookForMin(a: &Vec<int>, i: int) -> (m: int)
    requires 0 <= i < a.len()
    ensures i <= m < a.len()
    ensures forall|k: int| i <= k < a.len() ==> a.spec_index(k) >= a.spec_index(m)
{
    let mut m = i;
    let mut j = i + 1;
    
    while j < a.len()
        invariant 
            i <= m < a.len(),
            i <= j <= a.len(),
            forall|k: int| i <= k < j ==> a.spec_index(k) >= a.spec_index(m)
    {
        if a[j] < a[m] {
            m = j;
        }
        j = j + 1;
    }
    m
}

spec fn sorted(a: Vec<int>) -> bool
{
    sortedA(a, a.len() as int)
}

// Helper spec function to express that two sequences are permutations
spec fn is_permutation(a: Vec<int>, b: Vec<int>) -> bool {
    a.len() == b.len() &&
    forall|x: int| count_occurrences(a, x) == count_occurrences(b, x)
}

spec fn count_occurrences(a: Vec<int>, x: int) -> nat
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_occurrences(a.subrange(1, a.len() as int), x) + 
        if a.spec_index(0) == x { 1 } else { 0 }
    }
}

fn insertionSort(a: &mut Vec<int>)
    ensures sorted(a@)
{
    if a.len() <= 1 {
        return;
    }
    
    let mut i = 1;
    
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            sortedA(a@, i as int)
    {
        let key = a[i];
        let mut j = i;
        
        while j > 0 && a[j - 1] > key
            invariant 
                0 <= j <= i,
                j < a.len(),
                i < a.len(),
                // The part before j remains sorted
                forall|k: int| 0 <= k < j - 1 ==> a.spec_index(k) <= a.spec_index(k + 1),
                // Elements from j+1 to i are all >= key and sorted
                forall|k: int| j < k <= i ==> a.spec_index(k) >= key,
                forall|k: int| j < k < i ==> a.spec_index(k) <= a.spec_index(k + 1),
                // If j > 0, then a[j-1] > key (loop condition maintains this)
                j > 0 ==> a.spec_index(j - 1) > key
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        a[j] = key;
        
        // After insertion, prove sortedness up to i+1
        assert(sortedA(a@, (i + 1) as int)) by {
            // The key is now properly placed at position j
            assert(a.spec_index(j as int) == key);
            
            // All elements to the left of j are <= key
            assert(forall|k: int| 0 <= k < j ==> a.spec_index(k) <= key) by {
                if j > 0 {
                    // We know a[j-1] <= key because loop terminated
                    assert(a.spec_index(j - 1) <= key);
                    // And the left part was already sorted
                    assert(forall|k: int| 0 <= k < j - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
                }
            }
            
            // All elements to the right of j (up to i) are >= key
            assert(forall|k: int| j < k <= i ==> a.spec_index(k) >= key);
            
            // The whole range [0, i+1) is now sorted
            assert(forall|k: int| 0 <= k < i ==> a.spec_index(k) <= a.spec_index(k + 1)) by {
                // Left part [0, j) is sorted
                assert(forall|k: int| 0 <= k < j - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
                // Connection at j-1, j is good (a[j-1] <= key = a[j])
                if j > 0 {
                    assert(a.spec_index(j - 1) <= a.spec_index(j as int));
                }
                // Right part (j, i] is sorted and all >= key = a[j]
                assert(forall|k: int| j < k < i ==> a.spec_index(k) <= a.spec_index(k + 1));
                if j < i {
                    assert(a.spec_index(j as int) <= a.spec_index(j + 1));
                }
            }
        }
        
        i = i + 1;
    }
}

}