use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
proof fn lemma_swap_preserves_multiset(a: Seq<int>, i: int, j: int)
    requires
        0 <= i < j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() == a.to_multiset(),
{
    assert(a.update(i, a[j]).update(j, a[i]) =~= 
           a.update(i, a[j]).update(j, a[i]));
}

proof fn lemma_subrange_update(a: Seq<int>, i: int, j: int, k: int, v: int)
    requires
        0 <= i <= j <= a.len(),
        0 <= k < a.len(),
        !(i <= k < j),
    ensures
        a.update(k, v).subrange(i, j) == a.subrange(i, j),
{
}

proof fn lemma_swap_preserves_subrange(a: Seq<int>, c: int, f: int, i: int, j: int)
    requires
        0 <= c <= f <= a.len(),
        0 <= i < j < a.len(),
        !(c <= i < f) || !(c <= j < f),
    ensures
        a.update(i, a[j]).update(j, a[i]).subrange(c, f) == a.subrange(c, f),
{
    if !(c <= i < f) && !(c <= j < f) {
        lemma_subrange_update(a, c, f, i, a[j]);
        lemma_subrange_update(a.update(i, a[j]), c, f, j, a[i]);
    }
}

proof fn lemma_swap_within_subrange_preserves_multiset(a: Seq<int>, c: int, f: int, i: int, j: int)
    requires
        0 <= c <= i < j < f <= a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).subrange(c, f).to_multiset() == a.subrange(c, f).to_multiset(),
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    assert(swapped.subrange(c, f) =~= swapped.subrange(c, f));
    assert(a.subrange(c, f) =~= a.subrange(c, f));
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
    let mut i: usize = c;
    while i < f
        invariant
            c <= i <= f,
            a@.len() == old(a)@.len(),
            sorted_seg(a@, c as int, i as int),
            forall|k: int, l: int| c as int <= k < i as int && i as int <= l < f as int ==> a@[k] <= a@[l],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
    {
        let mut j: usize = f - 1;
        while j > i
            invariant
                c <= i < j < f,
                j >= i,
                a@.len() == old(a)@.len(),
                sorted_seg(a@, c as int, i as int),
                forall|k: int, l: int| c as int <= k < i as int && i as int <= l < f as int ==> a@[k] <= a@[l],
                forall|k: int| j as int < k && k < f as int ==> a@[j as int] <= a@[k],
                forall|k: int| j as int < k && k < f as int ==> a@[i as int] <= a@[k],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
        {
            if a[j - 1] > a[j] {
                let prev_a = a@;
                a.swap(j - 1, j);
                
                proof {
                    assert(a@ == prev_a.update((j - 1) as int, prev_a[j as int]).update(j as int, prev_a[(j - 1) as int]));
                    lemma_swap_within_subrange_preserves_multiset(prev_a, c as int, f as int, (j - 1) as int, j as int);
                    lemma_swap_preserves_subrange(prev_a, 0, c as int, (j - 1) as int, j as int);
                    lemma_swap_preserves_subrange(prev_a, f as int, prev_a.len() as int, (j - 1) as int, j as int);
                    
                    assert forall|k: int, l: int| c as int <= k < i as int && i as int <= l < f as int implies a@[k] <= a@[l] by {
                        if l == j as int {
                            assert(prev_a[k] <= prev_a[(j - 1) as int]);
                            assert(a@[l] == prev_a[(j - 1) as int]);
                        } else if l == (j - 1) as int {
                            assert(prev_a[k] <= prev_a[j as int]);
                            assert(a@[l] == prev_a[j as int]);
                        } else {
                            assert(a@[k] == prev_a[k]);
                            assert(a@[l] == prev_a[l]);
                        }
                    }
                    
                    assert forall|k: int| (j - 1) as int < k && k < f as int implies a@[(j - 1) as int] <= a@[k] by {
                        if k == j as int {
                            assert(a@[(j - 1) as int] == prev_a[j as int]);
                            assert(a@[k] == prev_a[(j - 1) as int]);
                            assert(prev_a[j as int] <= prev_a[(j - 1) as int]);
                        } else {
                            assert(a@[(j - 1) as int] == prev_a[j as int]);
                            assert(a@[k] == prev_a[k]);
                            assert(prev_a[j as int] <= prev_a[k]);
                        }
                    }
                    
                    assert forall|k: int| (j - 1) as int < k && k < f as int implies a@[i as int] <= a@[k] by {
                        if k == j as int {
                            assert(a@[k] == prev_a[(j - 1) as int]);
                            assert(prev_a[i as int] <= prev_a[(j - 1) as int]);
                        } else {
                            assert(a@[k] == prev_a[k]);
                        }
                    }
                }
            }
            j = j - 1;
        }
        
        proof {
            assert forall|k: int, l: int| c as int <= k <= l < (i + 1) as int implies a@[k] <= a@[l] by {
                if k < i as int && l < i as int {
                    assert(sorted_seg(a@, c as int, i as int));
                } else if k == i as int && l == i as int {
                    assert(a@[k] <= a@[l]);
                } else if k < i as int && l == i as int {
                    assert(a@[k] <= a@[l]);
                }
            }
            assert(sorted_seg(a@, c as int, (i + 1) as int));
        }
        
        i = i + 1;
    }
    
    assert(sorted_seg(a@, c as int, f as int));
}
// </vc-code>

fn main() {
}

}