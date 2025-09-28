use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

spec fn bubble_sort_inv(a: Seq<i32>, a_old: Seq<i32>, c: int, f: int, i: int, j: int) -> bool
    recommends 0 <= c <= i <= j <= f <= a.len(), 0 <= c <= f <= a_old.len()
{
    &&& sorted_seg(a, i, f)
    &&& a.subrange(i, f).to_multiset() == a_old.subrange(i, f).to_multiset()
    &&& a.subrange(c, i) == a_old.subrange(c, i)
    &&& a.subrange(f, a.len() as int) == a_old.subrange(f, a_old.len() as int)
    &&& forall|k: int| i <= k < j ==> a[k] <= a[j]
}

proof fn bubble_sort_lemma(a: Seq<i32>, c: int, f: int)
    requires
        0 <= c <= f <= a.len(),
    ensures
        sorted_seg(a, c, f) ==>
        a.subrange(c, f).to_multiset() == a.subrange(c, f).to_multiset() &&
        a.subrange(0, c) == a.subrange(0, c) &&
        a.subrange(f, a.len() as int) == a.subrange(f, a.len() as int)
{
}

proof fn swap_preserves_multiset(a: Seq<i32>, i: int, j: int) -> (b: Seq<i32>)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        b.to_multiset() == a.to_multiset(),
        b[i] == a[j],
        b[j] == a[i],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> b[k] == a[k]
{
    let mut b = a;
    b = b.insert(i, a[j]);
    b = b.insert(j, a[i]);
    b
}

proof fn bubble_pass_invariant(a: Seq<i32>, a_old: Seq<i32>, c: int, f: int, i: int, j: int) -> bool
    recommends 0 <= c <= i <= j <= f <= a.len(), 0 <= c <= f <= a_old.len()
{
    &&& sorted_seg(a, i, f)
    &&& a.subrange(i, f).to_multiset() == a_old.subrange(i, f).to_multiset()
    &&& a.subrange(c, i) == a_old.subrange(c, i)
    &&& a.subrange(f, a.len() as int) == a_old.subrange(f, a_old.len() as int)
    &&& forall|k: int| i <= k < j ==> a[k] <= a[j]
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
    let old_a = a@;
    proof {
        bubble_sort_lemma(old_a, c as int, f as int);
    }
    
    if c >= f {
        return;
    }
    
    let mut i = c;
    let mut j = f - 1;
    
    while i < f
        invariant
            c <= i <= f,
            sorted_seg(a@, i as int, f as int),
            a@.subrange(i as int, f as int).to_multiset() == old_a.subrange(i as int, f as int).to_multiset(),
            a@.subrange(0, i as int) == old_a.subrange(0, i as int),
            a@.subrange(f as int, a@.len() as int) == old_a.subrange(f as int, old_a.len() as int),
        decreases f - i
    {
        let mut k = j;
        while k > i
            invariant
                c <= i <= k + 1 <= f,
                sorted_seg(a@, i as int, f as int),
                a@.subrange(i as int, f as int).to_multiset() == old_a.subrange(i as int, f as int).to_multiset(),
                a@.subrange(0, i as int) == old_a.subrange(0, i as int),
                a@.subrange(f as int, a@.len() as int) == old_a.subrange(f as int, old_a.len() as int),
                forall|l: int| i as int <= l < k as int ==> a@[l] <= a@[k as int],
            decreases k - i
        {
            if a[k - 1] > a[k] {
                let temp = a[k - 1];
                a[k - 1] = a[k];
                a[k] = temp;
                proof {
                    let old_seq = a@;
                    let new_seq = swap_preserves_multiset(old_seq, (k - 1) as int, k as int);
                    assert(new_seq.to_multiset() == old_seq.to_multiset());
                }
            }
            k = k - 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}