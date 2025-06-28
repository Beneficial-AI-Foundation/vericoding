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
                // The array is sorted up to position j
                sortedA(a@, j as int),
                // Elements from j+1 to i are all greater than key
                forall|k: int| (j as int) < k <= (i as int) ==> a.spec_index(k) > key,
                // Elements from j+1 to i are sorted
                forall|k: int| (j as int) < k < (i as int) ==> a.spec_index(k) <= a.spec_index(k + 1),
                // If j > 0, then a[j-1] > key (from loop condition)
                j > 0 ==> a.spec_index((j - 1) as int) > key
        {
            a.set(j, a[j - 1]);
            j = j - 1;
        }
        
        a.set(j, key);
        
        // After insertion, prove that the array is sorted up to i+1
        assert(sortedA(a@, (i + 1) as int)) by {
            // Key insight: we need to prove sortedness across the insertion point
            if j > 0 {
                // If j > 0, then a[j-1] <= key (negation of loop condition)
                assert(a.spec_index((j - 1) as int) <= key);
            }
            if j < i {
                // Elements after j are > key, so key <= all elements after j
                assert(forall|k: int| (j as int) < k <= (i as int) ==> key <= a.spec_index(k));
            }
            // The sortedness follows from these properties
        }
        
        i = i + 1;
    }
}

}