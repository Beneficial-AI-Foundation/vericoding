// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
fn find_min_pos(a: &Vec<int>, i: usize, j: usize) -> (k: usize)
    requires
        i < j <= a.len(),
    ensures
        i <= k < j,
        forall|l: int| i as int <= l < j as int ==> a@[k as int] <= a@[l],
{
    let mut min_pos = i;
    let mut l = i + 1;
    while l < j
        invariant
            i <= min_pos < j,
            i < l <= j,
            j <= a.len(),
            forall|m: int| i as int <= m < l as int ==> a@[min_pos as int] <= a@[m],
        decreases j - l
    {
        if a[l] < a[min_pos] {
            min_pos = l;
        }
        l = l + 1;
    }
    min_pos
}
// </vc-helpers>

// <vc-spec>
fn sel_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a.len() == old(a).len(),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used a.swap() and a proof block to prove multiset preservation */
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            f <= a.len(),
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, i as int),
            forall|k: int, l: int| c as int <= k < i as int && i as int <= l < f as int ==> a@[k] <= a@[l],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
        decreases f - i
    {
        let min_pos = find_min_pos(a, i, f);
        
        let ghost old_a_at_loop = a@;
        a.swap(i, min_pos);

        proof {
            vstd::seq_lib::lemma_swap_preserves_subrange_multiset(old_a_at_loop, i as int, min_pos as int, c as int, f as int);
        }

        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}