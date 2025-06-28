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
        
        // First, shift elements to make space for key
        while j > 0 && a[j - 1] > key
            invariant 
                0 <= j <= i < a.len(),
                // Elements from j+1 to i+1 are shifted versions of original elements
                forall|k: int| (j as int) < k <= (i as int) ==> a@.spec_index(k) > key,
                // Elements before j remain sorted
                forall|k: int| 0 <= k < (j as int) - 1 ==> 
                    a@.spec_index(k) <= a@.spec_index(k + 1),
                // Connection between sorted part and shifted part
                j == 0 || a@.spec_index((j as int) - 1) <= key || 
                (forall|k: int| (j as int) <= k <= (i as int) ==> a@.spec_index(k) > key)
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert the key
        a[j] = key;
        
        // The array is now sorted up to i+1
        assert(sortedA(a@, (i + 1) as int)) by {
            // Key insight: we need to show all adjacent pairs are in order
            assert(forall|k: int| 0 <= k < i ==> 
                a@.spec_index(k) <= a@.spec_index(k + 1)) by {
                // This follows from our invariants:
                // 1. Elements before j were already sorted
                // 2. key is placed at the right position j
                // 3. Elements after j are all > key and maintain their relative order
            }
        }
        
        i = i + 1;
    }
}

}