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
proof fn lemma_swap_preserves_multiset<T>(v1: Seq<T>, v2: Seq<T>, i: int, j: int)
    requires 
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        i != j,
        v2.len() == v1.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k]
    ensures v1.to_multiset() == v2.to_multiset()
{
}

proof fn lemma_multiset_update<T>(v: Seq<T>, i: int, val: T)
    requires 0 <= i < v.len(), v[i] == val
    ensures v.update(i, val).to_multiset() == v.to_multiset()
{
}

proof fn lemma_sorted_min_first(v: Seq<i32>, min_idx: int, start: int, end: int)
    requires 
        0 <= start <= min_idx < end <= v.len(),
        forall|k: int| start <= k < end ==> v[min_idx] <= v[k],
        start < end
    ensures forall|k: int| start < k < end ==> v[min_idx] <= v[k]
{
}

proof fn lemma_sorted_prefix_extension(v: Seq<i32>, i: int)
    requires 
        0 <= i < v.len(),
        is_sorted(v.subrange(0, i)),
        forall|k: int| i <= k < v.len() ==> v[i] <= v[k]
    ensures is_sorted(v.subrange(0, i + 1))
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
    let ghost original_ns = ns@;
    let mut i = 0;
    while i < ns.len()
        invariant
            0 <= i <= ns.len(),
            is_sorted(ns@.subrange(0, i as int)),
            is_permutation2(original_ns, ns@),
            forall|j: int, k: int| 0 <= j < i && i <= k < ns.len() ==> ns@[j] <= ns@[k]
        decreases ns.len() - i
    {
        if i + 1 < ns.len() {
            let ghost old_ns = ns@;
            let min_idx = find_min_index(ns, i, ns.len());
            
            assert(forall|k: int| i <= k < ns.len() ==> ns@[min_idx as int] <= ns@[k]);
            
            if min_idx != i {
                let temp = ns[i];
                let min_val = ns[min_idx];
                ns.set(i, min_val);
                ns.set(min_idx, temp);
                
                proof {
                    lemma_swap_preserves_multiset(old_ns, ns@, i as int, min_idx as int);
                }
            } else {
                proof {
                    lemma_multiset_update(old_ns, i as int, ns@[i as int]);
                }
            }
            
            proof {
                lemma_sorted_prefix_extension(ns@, i as int);
            }
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}