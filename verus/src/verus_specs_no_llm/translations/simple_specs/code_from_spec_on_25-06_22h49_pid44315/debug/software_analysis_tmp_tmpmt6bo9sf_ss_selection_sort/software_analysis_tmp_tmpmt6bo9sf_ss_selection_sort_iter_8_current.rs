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
    // Verus can prove multiset equality from the swap properties
}

proof fn permutation_transitivity(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        is_permutation(a, b),
        is_permutation(b, c),
    ensures
        is_permutation(a, c)
{
    // Transitivity of equality on multisets
}

#[verifier::loop_isolation(false)]
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
        if i < ns.len() {
            let min_idx = find_min_index(ns, i, ns.len());
            
            // Swap elements using direct assignment
            let ghost pre_swap = ns@;
            let ghost orig_i = ns[i];
            let ghost orig_min = ns[min_idx];
            
            let temp = ns[i];
            ns[i] = ns[min_idx];
            ns[min_idx] = temp;
            
            // Proof that permutation is preserved after swap
            proof {
                if i != min_idx {
                    assert(ns@[i as int] == orig_min);
                    assert(ns@[min_idx as int] == orig_i);
                    assert(forall|k: int| 0 <= k < ns.len() && k != i && k != min_idx ==> ns@[k] == pre_swap[k]);
                    swap_preserves_permutation(pre_swap, ns@, i as int, min_idx as int);
                    permutation_transitivity(orig_seq, pre_swap, ns@);
                }
                
                // Prove that the new element at position i is minimal among remaining elements
                assert(forall|k: int| i <= k < ns.len() ==> ns[i as int] <= ns[k]);
                
                // Prove that sorted portion remains sorted
                assert(forall|j: int, k: int| 0 <= j <= k < i ==> ns[j] <= ns[k]);
                
                // Prove that sorted portion is still <= unsorted portion
                assert(forall|j: int, k: int| 0 <= j <= i && (i+1) <= k < ns.len() ==> ns[j] <= ns[k]);
            }
        }
        
        i = i + 1;
    }
}

}