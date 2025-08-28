use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg_full(a: Seq<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l < k < j ==> a[l] <= a[k]
}

proof fn lemma_sorted_seg_subrange(a: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
        sorted_seg_full(a, i, k),
    ensures
        sorted_seg_full(a, i, j),
        sorted_seg_full(a, j, k),
{
}

proof fn lemma_sorted_seg_trans(a: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
        sorted_seg_full(a, i, j),
        sorted_seg_full(a, j, k),
    ensures
        sorted_seg_full(a, i, k),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubbleSorta(a: &mut Vec<i32>, c: usize, f: usize) //f excluded
    requires 
        c <= f,
        f <= old(a).len(), //when c==f empty sequence
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn bubble_sort_a(a: &mut Vec<i32>, c: usize, f: usize)
    requires
        c <= f,
        f <= old(a).len(),
    ensures
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
{
    let mut i: usize = f;
    while i > c
        invariant
            c <= i,
            i <= f,
            sorted_seg(a@, i as int, f as int),
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
        decreases i,
    {
        let mut j: usize = c;
        while j < i
            invariant
                c <= j,
                j <= i,
                i <= f,
                sorted_seg(a@, i as int, f as int),
                forall|k: int| j as int <= k < i as int ==> a@[k] >= a@[j as int],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
            decreases i - j,
        {
            if j + 1 < i {
                if a[j] > a[j + 1] {
                    let temp = a[j];
                    a.set(j, a[j + 1]);
                    a.set(j + 1, temp);
                }
            }
            j = j + 1;
        }
        i = i - 1;
    }
}
// </vc-code>

fn main() {}

}