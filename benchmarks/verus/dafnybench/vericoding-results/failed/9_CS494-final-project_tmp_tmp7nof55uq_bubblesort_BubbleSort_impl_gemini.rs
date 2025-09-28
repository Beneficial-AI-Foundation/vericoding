// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|x: usize, y: usize| from <= x < y < to ==> a[x as int] <= a[y as int]
}

spec fn pivot(a: &Vec<i32>, to: usize, pvt: usize) -> bool
    recommends
        pvt < to,
        to <= a.len(),
{
    forall|x: usize, y: usize| 0 <= x < pvt < y < to ==> a[x as int] <= a[y as int]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed non-existent lemma names to correct ones from vstd */
proof fn swap_preserves_multiset(a: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let spec_old_a = old(a)@;
    a.swap(i, j);
    vstd::seq_lib::lemma_swap_permutes_seq(spec_old_a, i as int, j as int);
    vstd::seq::lemma_seq_permutes_implies_multiset_eq(a@, spec_old_a);
}
// </vc-helpers>

// <vc-spec>
fn BubbleSort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0,
    ensures 
        sorted(a, 0, a.len()),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, the compilation error was in the helper function */
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == a.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            sorted(a, 0, i),
            forall|k1: usize, k2: usize| k1 < i && i <= k2 < n ==> a[k1 as int] <= a[k2 as int],
        decreases n - i
    {
        let mut j: usize = n - 1;
        while j > i
            invariant
                0 <= i < n,
                i <= j < n,
                n == a.len(),
                a@.to_multiset() == old(a)@.to_multiset(),
                sorted(a, 0, i),
                forall|k1: usize, k2: usize| k1 < i && i <= k2 < n ==> a[k1 as int] <= a[k2 as int],
                forall|k: usize| j <= k < n ==> a[j as int] <= a[k as int],
            decreases j
        {
            if a[j - 1] > a[j] {
                swap_preserves_multiset(a, j - 1, j);
            }
            j = j - 1;
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}