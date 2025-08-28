use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn swapped_once(a: Seq<int>, b: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i < j < a.len() == b.len()
{
    b[i] == a[j] && b[j] == a[i] && 
    forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k]
}

proof fn swap_preserves_multiset(a: Seq<int>, b: Seq<int>, i: int, j: int)
    requires 
        0 <= i < j < a.len() == b.len(),
        swapped_once(a, b, i, j)
    ensures
        a.to_multiset() == b.to_multiset()
{
    assert(a.to_multiset().remove(a[i]).remove(a[j]) == b.to_multiset().remove(b[i]).remove(b[j]));
}

proof fn bubble_pass_maintains_sorted_prefix(a: Seq<int>, b: Seq<int>, start: int, end: int, sorted_until: int)
    requires
        0 <= start <= sorted_until <= end <= a.len(),
        sorted_seg(a, start, sorted_until),
        a.subrange(start, end).to_multiset() == b.subrange(start, end).to_multiset(),
        forall|k: int| start <= k < sorted_until - 1 ==> b[k] <= b[k + 1],
        forall|k: int| sorted_until <= k < end ==> b[sorted_until - 1] <= b[k]
    ensures
        sorted_seg(b, start, sorted_until)
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    if c >= f {
        return;
    }
    
    let mut i = c;
    while i < f - 1
        invariant 
            c <= i <= f - 1,
            sorted_seg(a@, c as int, i as int + 1),
            forall|k: int| i < k < f ==> a@[i as int] <= a@[k],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int)
        decreases f - i
    {
        let mut j = f - 1;
        while j > i
            invariant
                c <= i < j <= f - 1,
                sorted_seg(a@, c as int, i as int + 1),
                forall|k: int| j < k < f ==> a@[j as int] <= a@[k],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int)
            decreases j - i
        {
            if a[j - 1] > a[j] {
                let temp = a[j - 1];
                let val_j = a[j];
                a.set(j - 1, val_j);
                a.set(j, temp);
                
                proof {
                    let old_a = old(a)@;
                    swap_preserves_multiset(old(a)@, a@, (j - 1) as int, j as int);
                }
            }
            j -= 1;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}