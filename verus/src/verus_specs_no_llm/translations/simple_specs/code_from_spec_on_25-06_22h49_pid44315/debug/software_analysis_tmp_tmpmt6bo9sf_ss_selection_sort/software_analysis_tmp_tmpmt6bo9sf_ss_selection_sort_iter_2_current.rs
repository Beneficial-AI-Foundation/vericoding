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
            let temp = ns[i];
            ns.set(i, ns[min_idx]);
            ns.set(min_idx, temp);
            
            // Proof that permutation is preserved after swap
            proof {
                let pre_swap = old(ns)@;
                assert(is_permutation(pre_swap, ns@));
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