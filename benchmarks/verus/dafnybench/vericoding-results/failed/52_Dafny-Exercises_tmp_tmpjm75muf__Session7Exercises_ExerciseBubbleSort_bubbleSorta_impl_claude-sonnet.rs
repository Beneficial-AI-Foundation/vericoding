use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg_trans(a: Seq<i32>, i: int, j: int, k: int) -> bool
{
    sorted_seg(a, i, j) && sorted_seg(a, j, k) && (i < j < k ==> a[j-1] <= a[j]) ==> sorted_seg(a, i, k)
}

proof fn lemma_sorted_seg_extend(a: Seq<i32>, i: int, j: int)
    requires 
        0 <= i < j <= a.len(),
        sorted_seg(a, i, j-1),
        forall|k: int| i <= k < j-1 ==> a[k] <= a[j-1]
    ensures sorted_seg(a, i, j)
{
    assert forall|l: int, k: int| i <= l <= k < j implies a[l] <= a[k] by {
        if l <= k < j-1 {
            assert(a[l] <= a[k]);
        } else if l < j-1 && k == j-1 {
            assert(a[l] <= a[k]);
        }
    }
}

proof fn lemma_swap_preserves_multiset(a: Seq<i32>, b: Seq<i32>, i: int, j: int, start: int, end: int)
    requires
        0 <= start <= i < j < end <= a.len(),
        a.len() == b.len(),
        b == a.update(i, a[j]).update(j, a[i]),
    ensures
        a.subrange(start, end).to_multiset() == b.subrange(start, end).to_multiset()
{
    assert(a.subrange(start, end).to_multiset() =~= b.subrange(start, end).to_multiset());
}

proof fn lemma_bubble_step_sorted(a: Seq<i32>, b: Seq<i32>, i: int, start: int, end: int)
    requires
        0 <= start <= i < i + 1 < end <= a.len(),
        sorted_seg(a, start, i + 1),
        a[i] > a[i + 1],
        b == a.update(i, a[i + 1]).update(i + 1, a[i]),
    ensures
        sorted_seg(b, start, i + 1)
{
    assert forall|l: int, k: int| start <= l <= k < i + 1 implies b[l] <= b[k] by {
        if l != i && k != i {
            assert(b[l] == a[l] && b[k] == a[k]);
        } else if l == i {
            assert(b[l] == a[i + 1] && b[k] <= a[i]);
        }
    }
}

proof fn lemma_swap_elements(v: &mut Vec<i32>, old_v: Seq<i32>, i: usize, j: usize)
    requires
        old(v)@ == old_v,
        i < old(v).len(),
        j < old(v).len(),
        i != j,
    ensures
        v.len() == old_v.len(),
        v@ == old_v.update(i as int, old_v[j as int]).update(j as int, old_v[i as int]),
{
}
// </vc-helpers>

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
// <vc-code>
{
    if c >= f {
        return;
    }
    
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            f <= a.len(),
            f <= old(a).len(),
            sorted_seg(a@, c as int, i as int),
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
            a.len() == old(a).len(),
    {
        let mut j = i + 1;
        while j < f
            invariant
                c <= i < j <= f,
                f <= a.len(),
                f <= old(a).len(),
                sorted_seg(a@, c as int, i as int + 1),
                forall|k: int| (c as int) <= k <= (i as int) && (j as int) <= k < (f as int) ==> a@[i as int] <= a@[k],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
                a.len() == old(a).len(),
        {
            if a[i] > a[j] {
                let old_a = a@;
                let temp = a[i];
                a.set(i, a[j]);
                a.set(j, temp);
                
                proof {
                    lemma_swap_preserves_multiset(old_a, a@, i as int, j as int, c as int, f as int);
                }
            }
            j += 1;
        }
        
        proof {
            lemma_sorted_seg_extend(a@, c as int, i as int + 1);
        }
        
        i += 1;
    }
}
// </vc-code>

fn main() {}

}