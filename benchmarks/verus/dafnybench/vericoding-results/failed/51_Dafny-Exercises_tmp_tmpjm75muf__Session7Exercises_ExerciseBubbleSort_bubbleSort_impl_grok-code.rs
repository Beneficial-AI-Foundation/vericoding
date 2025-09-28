use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    requires 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
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
    let bubble_start: usize = c;
    let bubble_end: usize = f;
    let mut pass: usize = 0;
    let mut swapped: bool = true;
    while pass < bubble_end - bubble_start && swapped
        invariant
            pass <= bubble_end - bubble_start,
            sorted_seg(a@, (bubble_end - pass) as int, bubble_end as int),
            a@.subrange(c as int, bubble_end as int).to_multiset() == old(a)@.subrange(c as int, bubble_end as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(bubble_end as int, a@.len() as int) == old(a)@.subrange(bubble_end as int, old(a)@.len() as int),
            a@.len() == old(a)@.len(),
        decreases bubble_end - bubble_start - pass
    {
        swapped = false;
        let mut j: usize = bubble_start + 1;
        while j < bubble_end - pass
            invariant
                pass <= bubble_end - bubble_start,
                bubble_start + 1 <= j <= bubble_end - pass,
                sorted_seg(a@, (bubble_end - pass) as int, bubble_end as int),
                a@.subrange(c as int, bubble_end as int).to_multiset() == old(a)@.subrange(c as int, bubble_end as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(bubble_end as int, a@.len() as int) == old(a)@.subrange(bubble_end as int, old(a)@.len() as int),
                a@.len() == old(a)@.len(),
            decreases bubble_end - pass - j
        {
            if a@[j] < a@[j - 1] {
                let temp = a[j - 1];
                let temp2 = a[j];
                a.set(j - 1, temp2);
                a.set(j, temp);
                swapped = true;
            }
            j += 1;
        }
        pass += 1;
    }
    proof {
        assert(sorted_seg(a@, c as int, f as int));
        assert(a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset());
        assert(a@.subrange(0, c as int) == old(a)@.subrange(0, c as int));
        assert(a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int));
    }
}
// </vc-code>

fn main() {
}

}