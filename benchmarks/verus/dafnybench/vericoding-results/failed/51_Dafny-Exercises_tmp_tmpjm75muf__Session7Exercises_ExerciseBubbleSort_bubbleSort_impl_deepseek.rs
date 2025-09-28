use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn reverse_sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] >= a[k]
}

proof fn bubble_sort_helper(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= a.len(),
        i <= k < j,
        sorted_seg(a, i, k + 1),
        reverse_sorted_seg(a, k, j),
        forall|l: int| i <= l < k ==> a[l] <= a[k],
    ensures
        sorted_seg(a, i, j),
    decreases j - k
{
    if k < j - 1 {
        assert(a[k] >= a[k + 1]);
        if a[k] > a[k + 1] {
            let a_swapped = a.update(k, a[k + 1]).update(k + 1, a[k]);
            bubble_sort_helper(a_swapped, i, j, k + 1);
        } else {
            bubble_sort_helper(a, i, j, k + 1);
        }
    }
}

proof fn bubble_sort_invariant(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= a.len(),
        i <= k <= j,
        sorted_seg(a, i, k),
        reverse_sorted_seg(a, k, j),
        forall|l: int, m: int| i <= l < k <= m < j ==> a[l] <= a[m],
    ensures
        a.subrange(i, j).to_multiset() == old(a).subrange(i, j).to_multiset(),
    decreases j - k
{
}

proof fn swap_preserves_multiset(a: Seq<int>, i: int, j: int, idx: int) 
    requires
        0 <= i <= j <= a.len(),
        i <= idx < j - 1,
    ensures
        a.update(idx, a[idx + 1]).update(idx + 1, a[idx]).subrange(i, j).to_multiset() 
        == a.subrange(i, j).to_multiset()
{
}

proof fn seq_to_multiset_preserved_after_update(a: Seq<int>, i: int, j: int, idx: int, val1: int, val2: int)
    requires
        0 <= i <= j <= a.len(),
        i <= idx < j - 1,
    ensures
        a.update(idx, val1).update(idx + 1, val2).subrange(i, j).to_multiset() 
        == a.subrange(i, j).to_multiset()
{
}

proof fn preserves_multiset(a: Seq<int>, i: int, j: int)
    ensures
        a.subrange(i, j).to_multiset() == old(a).subrange(i, j).to_multiset()
{
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
    let mut i_var = c;
    let mut j_var = f;
    
    while i_var < j_var
        invariant
            0 <= c <= i_var <= j_var <= f <= a@.len(),
            sorted_seg(a@, c as int, i_var as int),
            reverse_sorted_seg(a@, j_var as int - 1, j_var as int),
            forall|l: int, m: int| c as int <= l < i_var as int <= m < j_var as int ==> a@[l] <= a@[m],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
        decreases j_var - i_var
    {
        let mut k = i_var;
        
        while k < j_var - 1
            invariant
                i_var <= k <= j_var - 1,
                sorted_seg(a@, c as int, i_var as int),
                reverse_sorted_seg(a@, k as int, j_var as int),
                forall|l: int, m: int| c as int <= l < i_var as int <= m < j_var as int ==> a@[l] <= a@[m],
                forall|l: int| i_var as int <= l < k as int ==> a@[l] <= a@[k as int],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
            decreases j_var - 1 - k
        {
            if a[k] > a[k + 1] {
                let temp = a[k];
                a[k] = a[k + 1];
                a[k + 1] = temp;
                proof {
                    swap_preserves_multiset(a@, c as int, f as int, k as int);
                }
            }
            k += 1;
        }
        
        j_var -= 1;
    }
}
// </vc-code>

fn main() {
}

}