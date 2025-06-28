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
        
        // Store the original value at position j for the invariant
        let ghost original_a = a@;
        
        while j > 0 && a[j - 1] > key
            invariant 
                0 <= j <= i,
                j < a.len(),
                i < a.len(),
                // The elements from j+1 to i+1 have been shifted right by 1
                forall|k: int| (j as int) + 1 <= k <= (i as int) ==> 
                    a.spec_index(k) == original_a.spec_index(k - 1),
                // Elements from j+1 to i are all greater than key
                forall|k: int| (j as int) + 1 <= k <= (i as int) ==> a.spec_index(k) > key,
                // The portion before j is still sorted
                sortedA(a@, j as int),
                // The portion after insertion point maintains relative order
                forall|k: int| (j as int) + 1 <= k < (i as int) ==> 
                    a.spec_index(k) <= a.spec_index(k + 1)
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        a[j] = key;
        
        // Prove that the array is sorted up to i+1
        assert(forall|k: int| 0 <= k < j ==> a.spec_index(k) <= key) by {
            if j > 0 {
                assert(!(a.spec_index((j-1) as int) > key));
                assert(sortedA(a@, j as int));
            }
        };
        
        assert(forall|k: int| (j as int) < k <= (i as int) ==> key <= a.spec_index(k)) by {
            assert(forall|k: int| (j as int) + 1 <= k <= (i as int) ==> a.spec_index(k) > key);
        };
        
        assert(sortedA(a@, (i + 1) as int)) by {
            assert(forall|k: int| 0 <= k < (i as int) ==> a.spec_index(k) <= a.spec_index(k + 1));
        };
        
        i = i + 1;
    }
}

}