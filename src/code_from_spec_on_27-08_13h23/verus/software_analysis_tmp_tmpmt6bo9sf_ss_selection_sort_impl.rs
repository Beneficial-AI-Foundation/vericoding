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
proof fn lemma_swap_preserves_multiset(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < b.len(),
        a.len() == b.len(),
    ensures
        (a.subrange(0, i) + seq![b[j]] + a.subrange(i + 1, a.len() as int)).to_multiset() ==
        (b.subrange(0, j) + seq![a[i]] + b.subrange(j + 1, b.len() as int)).to_multiset(),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn selection_sort(ns: &mut Vec<i32>) 
    requires old(ns).len() >= 0
    ensures 
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn selection_sort(ns: &mut Vec<i32>)
    requires
        ns.len() >= 0,
    ensures
        is_sorted(ns@),
        is_permutation2(old(ns)@, ns@),
{
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            i <= ns.len(),
            forall|k: int, l: int| 0 <= k <= l < i ==> ns@[k] <= ns@[l],
            is_permutation2(old(ns)@, ns@),
    {
        let min_idx = find_min_index(ns, i, ns.len());
        let i_int = i as int;
        let min_idx_int = min_idx as int;
        proof {
            lemma_swap_preserves_multiset(old(ns)@, ns@, i_int, min_idx_int);
        }
        ns.swap(i, min_idx);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}