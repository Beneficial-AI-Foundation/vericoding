use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
proof fn bubble_sort_terminates(a: Seq<int>, c: int, f: int) 
    requires 0 <= c <= f <= a.len()
    decreases f - c, f
{
    if c < f {
        bubble_sort_terminates(a, c + 1, f);
    }
}

proof fn bubble_sort_inner_terminates(a: Seq<int>, i: int, f: int) 
    requires 0 <= i < f <= a.len()
    decreases f - i
{
    if i < f - 1 {
        bubble_sort_inner_terminates(a, i + 1, f);
    }
}

proof fn bubble_sort_outer_loop_invariant(a: Seq<int>, c: int, f: int) 
    requires 0 <= c <= f <= a.len()
    ensures sorted_seg(a, f, f)
{
    assert(sorted_seg(a, f, f));
}

proof fn bubble_sort_inner_loop_invariant(a: Seq<int>, i: int, f: int) 
    requires 0 <= i <= f <= a.len()
    ensures sorted_seg(a, f, f)
{
    assert(sorted_seg(a, f, f));
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        0 <= c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
// </vc-spec>
// <vc-code>
{
    let mut i = c;
    while i < f
        invariant
            0 <= c <= i <= f <= a.len(),
            sorted_seg(a@, c as int, i as int),
            a@.subrange(c as int, i as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(i as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
        decreases f - i
    {
        let mut j = c;
        while j < f - 1 - (i - c)
            invariant
                0 <= c <= i <= f <= a.len(),
                0 <= c <= j <= f - (i - c) <= f,
                sorted_seg(a@, c as int, j as int),
                a@.subrange(c as int, j as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(j as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
                forall|k: int| j <= k < f - (i - c) ==> a@[k] <= a@[f - (i - c)],
            decreases f - (i - c) - j
        {
            if a[j] > a[j + 1] {
                a.swap(j, j + 1);
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}