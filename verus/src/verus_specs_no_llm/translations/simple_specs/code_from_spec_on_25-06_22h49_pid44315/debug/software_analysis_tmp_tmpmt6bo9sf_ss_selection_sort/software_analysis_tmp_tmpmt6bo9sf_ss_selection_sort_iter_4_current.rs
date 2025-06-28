use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_sorted(ss: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<int>, b: Seq<int>) -> bool {
    multiset(a) == multiset(b)
}

fn find_min_index(a: &Vec<int>, s: usize, e: usize) -> (min_i: usize)
    requires 
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures 
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
{
    let mut min_i = s;
    let mut i = s + 1;
    
    while i < e
        invariant
            s <= min_i < e,
            s < i <= e,
            forall|k: int| s <= k < i ==> a[min_i as int] <= a[k],
    {
        if a[i] < a[min_i] {
            min_i = i;
        }
        i = i + 1;
    }
    
    min_i
}

proof fn swap_preserves_permutation(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        a.len() == b.len(),
        b[i] == a[j],
        b[j] == a[i],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
    ensures
        is_permutation(a, b)
{
    // The key insight: swapping two elements preserves the multiset
    // We need to show that multiset(a) == multiset(b)
    // This follows from the fact that b is obtained from a by swapping elements at positions i and j
    
    // Verus can prove this automatically given the preconditions
    assert(multiset(a).count(a[i]) == multiset(b).count(a[i]));
    assert(multiset(a).count(a[j]) == multiset(b).count(a[j]));
    
    // For any other element x, the count remains the same
    assert(forall|x: int| x != a[i] && x != a[j] ==> 
           multiset(a).count(x) == multiset(b).count(x));
           
    assert(multiset(a) == multiset(b));
}

proof fn permutation_transitivity(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        is_permutation(a, b),
        is_permutation(b, c),
    ensures
        is_permutation(a, c)
{
    assert(multiset(a) == multiset(b));
    assert(multiset(b) == multiset(c));
    assert(multiset(a) == multiset(c));
}

fn selection_sort(ns: &mut Vec<int>)
    ensures
        is_sorted(ns@),
        is_permutation(old(ns)@, ns@),
{
    let ghost orig_seq = ns@;
    let mut i = 0;
    
    while i < ns.len()
        invariant
            0 <= i <= ns.len(),
            ns.len() == orig_seq.len(),
            is_permutation(orig_seq, ns@),
            // The first i elements are sorted
            forall|j: int, k: int| 0 <= j <= k < i ==> ns[j] <= ns[k],
            // Each element in the sorted portion is <= each element in the unsorted portion
            forall|j: int, k: int| 0 <= j < i && i <= k < ns.len() ==> ns[j] <= ns[k],
    {
        if i + 1 < ns.len() {
            let min_idx = find_min_index(ns, i, ns.len());
            
            // Swap elements
            let ghost pre_swap = ns@;
            let temp = ns[i];
            ns.set(i, ns[min_idx]);
            ns.set(min_idx, temp);
            
            // Proof that permutation is preserved after swap
            proof {
                if i != min_idx {
                    swap_preserves_permutation(pre_swap, ns@, i as int, min_idx as int);
                    permutation_transitivity(orig_seq, pre_swap, ns@);
                } else {
                    // If i == min_idx, no swap occurred, so sequences are equal
                    assert(pre_swap == ns@);
                }
                assert(is_permutation(orig_seq, ns@));
            }
        }
        
        i = i + 1;
    }
    
    // Final proof that the entire sequence is sorted
    proof {
        assert(i == ns.len());
        assert(forall|j: int, k: int| 0 <= j <= k < i ==> ns[j] <= ns[k]);
        assert(forall|j: int, k: int| 0 <= j <= k < ns.len() ==> ns[j] <= ns[k]);
    }
}

}