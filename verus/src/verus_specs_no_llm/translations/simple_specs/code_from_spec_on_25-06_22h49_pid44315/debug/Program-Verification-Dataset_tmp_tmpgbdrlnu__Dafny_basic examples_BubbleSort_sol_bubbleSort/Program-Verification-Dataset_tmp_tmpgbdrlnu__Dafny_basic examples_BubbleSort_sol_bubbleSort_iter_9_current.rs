use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to check if entire array is sorted
spec fn sorted(a: Vec<int>) -> bool {
    sorted_between(a, 0, a.len() as int)
}

// Predicate to check if array is sorted between indices
spec fn sorted_between(a: Vec<int>, from: int, to: int) -> bool {
    &&& 0 <= from <= to
    &&& to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Spec function to get multiset from vector
spec fn to_multiset(a: Vec<int>) -> Multiset<int> {
    Multiset::from_seq(a@)
}

// Helper lemma for multiset preservation during swaps
proof fn lemma_swap_preserves_multiset(a: Vec<int>, i: usize, j: usize, new_a: Vec<int>)
    requires
        i < a.len(),
        j < a.len(),
        i != j,
        new_a.len() == a.len(),
        new_a[i as int] == a[j as int],
        new_a[j as int] == a[i as int],
        forall|k: int| 0 <= k < a.len() && k != i as int && k != j as int ==> new_a[k] == a[k]
    ensures
        to_multiset(new_a) == to_multiset(a)
{
    assert(new_a@ =~= a@.update(i as int, a[j as int]).update(j as int, a[i as int]));
}

// Helper lemma to establish that after inner loop, largest element is in correct position
proof fn lemma_bubble_establishes_max(a: Vec<int>, start: int, end: int)
    requires
        0 <= start < end <= a.len(),
        forall|k: int| start <= k < end - 1 ==> a[k] <= a[end - 1]
    ensures
        forall|k: int| start <= k < end ==> a[k] <= a[end - 1]
{
    // The largest element is now at position end-1
}

// Helper lemma for maintaining sorted suffix
proof fn lemma_maintain_sorted_suffix(a: Vec<int>, old_a: Vec<int>, pos: int, n: int)
    requires
        0 <= pos < n <= a.len(),
        a.len() == old_a.len(),
        sorted_between(old_a, pos + 1, n),
        forall|k: int| pos + 1 <= k < n ==> a[k] == old_a[k],
        forall|k: int| 0 <= k <= pos ==> a[k] <= a[pos]
    ensures
        sorted_between(a, pos, n)
{
    // The sorted suffix is maintained and extended
}

// Method to perform bubble sort
fn bubble_sort(a: &mut Vec<int>)
    requires 
        a.len() > 0
    ensures 
        sorted(*a),
        to_multiset(*a) == to_multiset(*old(a))
{
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            a.len() == n,
            to_multiset(*a) == to_multiset(*old(a)),
            // Elements from n-i to n-1 are sorted and in final position
            sorted_between(*a, (n - i) as int, n as int),
            // All elements in sorted part are >= elements in unsorted part
            forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> a[k] <= a[l]
        decreases n - i
    {
        if i < n - 1 {
            let mut j: usize = 0;
            let limit = n - 1 - i;
            
            // Store the old state before inner loop
            let ghost old_outer_a = *a;
            
            while j < limit
                invariant
                    j <= limit,
                    limit == n - 1 - i,
                    i < n,
                    a.len() == n,
                    to_multiset(*a) == to_multiset(old_outer_a),
                    to_multiset(old_outer_a) == to_multiset(*old(a)),
                    // Sorted suffix is preserved
                    sorted_between(*a, (n - i) as int, n as int),
                    forall|k: int| (n - i) as int <= k < n as int ==> a[k] == old_outer_a[k],
                    // Separation property maintained
                    forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> old_outer_a[k] <= a[l],
                    // Largest element so far is bubbled up
                    j < n,
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
                decreases limit - j
            {
                if a[j] > a[j + 1] {
                    // Capture old state for proof
                    let ghost old_inner_a = *a;
                    
                    // Perform swap
                    let temp = a[j];
                    a[j] = a[j + 1];
                    a[j + 1] = temp;
                    
                    // Prove multiset preservation
                    proof {
                        lemma_swap_preserves_multiset(old_inner_a, j, j + 1, *a);
                        assert(to_multiset(*a) == to_multiset(old_inner_a));
                        assert(to_multiset(*a) == to_multiset(old_outer_a)) by {
                            assert(to_multiset(old_inner_a) == to_multiset(old_outer_a));
                        }
                    }
                }
                
                j += 1;
                
                // Maintain the bubbling property
                proof {
                    if j > 0 {
                        assert(a[j - 1] <= a[j as int]);
                    }
                }
            }
            
            // After inner loop, prove that we have the maximum element at position n-1-i
            proof {
                if limit > 0 {
                    lemma_bubble_establishes_max(*a, 0, (n - i) as int);
                    assert(forall|k: int| 0 <= k < (n - i) as int ==> a[k] <= a[(n - i - 1) as int]);
                    
                    // Extend the sorted region
                    lemma_maintain_sorted_suffix(*a, old_outer_a, (n - i - 1) as int, n as int);
                }
            }
        }
        
        i += 1;
    }
    
    // Final proof that the entire array is sorted
    proof {
        assert(i == n);
        assert(sorted_between(*a, 0, n as int));
        assert(sorted(*a));
    }
}

}