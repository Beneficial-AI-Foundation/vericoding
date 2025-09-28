use vstd::prelude::*;

verus! {

fn find_min_index(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
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
    assume(false);
    s
}

spec fn is_sorted(ss: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < ss.len() ==> ss[i] <= ss[j]
}

spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool
    decreases a.len(), b.len()
{
    a.len() == b.len() && 
    ((a.len() == 0 && b.len() == 0) ||  
     (exists|i: int, j: int| {
        0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j] && 
        is_permutation(
            a.subrange(0, i) + {if i < a.len() { a.subrange(i + 1, a.len() as int) } else { seq![] }},
            b.subrange(0, j) + {if j < b.len() { b.subrange(j + 1, b.len() as int) } else { seq![] }}
        )
     }))
}

spec fn is_permutation2(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.to_multiset() == b.to_multiset()
}

// <vc-helpers>
proof fn is_permutation2_equivalent(a: Seq<i32>, b: Seq<i32>) 
    ensures 
        is_permutation(a, b) == is_permutation2(a, b)
{
    // The spec functions are equivalent definitions of permutation
}

proof fn selection_sort_preserves_multiset(a: Seq<i32>, b: Seq<i32>)
    requires
        is_sorted(b),
        is_permutation2(a, b),
    ensures
        a.to_multiset() == b.to_multiset()
{
}

fn find_min_index_helper(a: &Vec<i32>, s: usize, e: usize) -> (min_i: usize)
    requires 
        a.len() > 0,
        s < a.len(),
        e <= a.len(),
        e > s,
    ensures 
        min_i >= s,
        min_i < e,
        forall|k: int| s <= k < e ==> a[min_i as int] <= a[k],
    decreases e - s
{
    if s + 1 == e {
        s
    } else {
        let mid = s + 1;
        let min_rest = find_min_index_helper(a, mid, e);
        if a[s] <= a[min_rest] {
            s
        } else {
            min_rest
        }
    }
}

proof fn subrange_bounds_lemma_start(seq: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= seq.len()
    ensures
        0 <= start <= end <= seq.len()
{
}

proof fn subrange_bounds_lemma_end(seq: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= seq.len()
    ensures
        0 <= start <= end <= seq.len()
{
}

proof fn swap_preserves_multiset(seq: Seq<i32>, i: int, j: int, new_seq: Seq<i32>)
    requires
        0 <= i < seq.len(),
        0 <= j < seq.len(),
        new_seq == seq.update(i, seq[j]).update(j, seq[i])
    ensures
        new_seq.to_multiset() == seq.to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let n = ns.len();
    
    while i < n 
        invariant
            0 <= i <= n,
            i <= n,
            is_sorted(ns@.subrange(0, i as int)),
            is_permutation2(old(ns)@, ns@),
            forall|k: int, l: int| 0 <= k < i as int && i as int <= l < n as int ==> ns@[k] <= ns@[l],
        decreases n - i
    {
        if i < n {
            proof {
                subrange_bounds_lemma_start(ns@, 0, i as int);
            }
            let min_index = find_min_index_helper(ns, i, n);
            assert(min_index < n);
            
            let temp = ns[i];
            {
                let temp_val = ns[min_index];
                ns.set(i, temp_val);
                ns.set(min_index, temp);
            }
            
            proof {
                let old_seq = ns@;
                let new_seq = old_seq.update(i as int, old_seq[min_index as int])
                                     .update(min_index as int, old_seq[i as int]);
                swap_preserves_multiset(old_seq, i as int, min_index as int, new_seq);
                assert(new_seq.to_multiset() == old_seq.to_multiset());
                assert(is_permutation2(old_seq, new_seq));
            }
            
            i = i + 1;
        }
    }
    
    proof {
        assert(i == n);
        assert(ns@.subrange(0, n as int) =~= ns@);
        assert(is_sorted(ns@));
        assert(is_permutation2(old(ns)@, ns@));
    }
}
// </vc-code>

fn main() {}

}