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
        
        // Store the original value at position j for the loop invariant
        let ghost old_a = a@;
        
        while j > 0 && a[j - 1] > key
            invariant 
                0 <= j <= i,
                j < a.len(),
                i < a.len(),
                // The key value is preserved
                key == old_a.spec_index(i as int),
                // Array length is preserved
                a.len() == old_a.len(),
                // Elements before j are unchanged from original
                forall|k: int| 0 <= k < j ==> a.spec_index(k) == old_a.spec_index(k),
                // Elements from j to i are shifted versions of elements from j-1 to i-1 in original
                forall|k: int| j < k <= i ==> a.spec_index(k) == old_a.spec_index((k - 1) as int),
                // Elements after i are unchanged
                forall|k: int| i < k < a.len() ==> a.spec_index(k) == old_a.spec_index(k),
                // The part before j remains sorted
                sortedA(a@, j as int),
                // If j > 0, then a[j-1] > key (loop condition)
                j > 0 ==> a.spec_index((j - 1) as int) > key
        {
            a.set(j, a[j - 1]);
            j = j - 1;
        }
        
        a.set(j, key);
        
        // Prove that the array is sorted up to i+1
        assert(sortedA(a@, (i + 1) as int)) by {
            // After the loop, either j == 0 or a[j-1] <= key
            if j > 0 {
                assert(a.spec_index((j - 1) as int) <= key);
            }
            
            // The key is now at position j
            assert(a.spec_index(j as int) == key);
            
            // Elements after j up to i are the shifted elements, all >= key
            assert(forall|k: int| j < k <= i ==> a.spec_index(k) >= key);
            
            // Sortedness is maintained
            assert(forall|k: int| 0 <= k < (i + 1) - 1 ==> a.spec_index(k) <= a.spec_index(k + 1)) by {
                assert(forall|k: int| 0 <= k < j - 1 ==> a.spec_index(k) <= a.spec_index(k + 1));
                if j > 0 {
                    assert(a.spec_index((j - 1) as int) <= a.spec_index(j as int));
                }
                assert(forall|k: int| j <= k < i ==> a.spec_index(k) <= a.spec_index(k + 1));
            }
        }
        
        i = i + 1;
    }
}

}