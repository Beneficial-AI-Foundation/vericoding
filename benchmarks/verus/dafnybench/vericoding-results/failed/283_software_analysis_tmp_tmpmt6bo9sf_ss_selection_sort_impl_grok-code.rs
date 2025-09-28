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
    let mut min_i: usize = s;
    let mut i: usize = s + 1;
    while i < e 
        invariant
            min_i >= s && min_i < i && i > s && i <= e,
            forall|k: int| s <= k < i ==> #[trigger] a@[min_i as int] <= #[trigger] a@[k],
    {
        if a[i] < a[min_i] {
            min_i = i;
        }
        i = i + 1;
    }
    min_i
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
    if ns.len() <= 1 {
        return;
    }
    let mut i: usize = 0;
    while i < ns.len() - 1
        invariant
            i <= ns.len() - 1,
            ns@.to_multiset() == old(ns)@.to_multiset(),
            forall|k: int, l: int| #![trigger] (0 <= k <= l < ns.len()) &&
                (k < i as int ==> ns@[k] <= ns@[l])
    {
        let min_idx = find_min_index(&*ns, i, ns.len());
        proof {
            // assert that min_idx is valid and properties hold
            assert(min_idx >= i && min_idx < ns.len());
        }
        ns.swap(i, min_idx);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}