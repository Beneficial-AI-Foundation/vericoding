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

// Helper spec function to check if elements in a range are all greater than a value
spec fn all_greater_than(a: Vec<int>, start: int, end: int, val: int) -> bool
    requires 0 <= start <= end <= a.len()
{
    forall|k: int| start <= k < end ==> a.spec_index(k) > val
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
                // The portion from 0 to j is sorted
                sortedA(a@, j as int),
                // All elements from j+1 to i are greater than key
                forall|k: int| (j as int) + 1 <= k <= (i as int) ==> a.spec_index(k) > key,
                // The shifted elements maintain their relative order
                forall|k: int| (j as int) + 1 <= k < (i as int) ==> 
                    a.spec_index(k) <= a.spec_index(k + 1)
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        a[j] = key;
        
        // Prove that inserting key at position j maintains sortedness
        proof {
            // After insertion, the array should be sorted up to i+1
            assert(forall|k: int| 0 <= k < (i as int + 1) - 1 ==> 
                a@.spec_index(k) <= a@.spec_index(k + 1)) by {
                
                // Case 1: k < j - 1 (before insertion point)
                if (0 <= k < (j as int) - 1) {
                    assert(sortedA(a@, j as int));
                }
                
                // Case 2: k == j - 1 (transition to key)
                if (k == (j as int) - 1 && j > 0) {
                    // We know that a[j-1] <= key because the while loop terminated
                    assert(!(a@.spec_index((j-1) as int) > key));
                }
                
                // Case 3: k == j (transition from key)
                if (k == j as int && j < i) {
                    // We know key < all elements from j+1 to i
                    assert(forall|m: int| (j as int) + 1 <= m <= (i as int) ==> 
                        a@.spec_index(m) > key);
                }
                
                // Case 4: k > j (after insertion point)
                if (k > j as int && k < i as int) {
                    // These elements were shifted but maintain relative order
                    assert(forall|m: int| (j as int) + 1 <= m < (i as int) ==> 
                        a@.spec_index(m) <= a@.spec_index(m + 1));
                }
            }
        }
        
        i = i + 1;
    }
}

}