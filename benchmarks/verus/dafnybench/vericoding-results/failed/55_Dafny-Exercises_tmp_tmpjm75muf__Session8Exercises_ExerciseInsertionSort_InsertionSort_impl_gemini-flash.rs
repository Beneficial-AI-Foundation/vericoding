use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn multiset_same(a: &Vec<i32>, b: &Vec<i32>) -> bool
{
    a@.to_multiset() == b@.to_multiset()
}

proof fn lemma_insert_stays_same(a: &mut Vec<i32>, i: int, x: i32)
    requires
        0 <= i < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let old_a = old(a);
    a.set(i as usize, x);
    assert(a@.to_multiset() == old_a@.to_multiset()); // This is trivially true for set
}

proof fn lemma_multiset_insert_swap_stable(a: &mut Vec<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let old_a = old(a);
    let temp = a[i as usize];
    a.set(i as usize, a[j as usize]);
    a.set(j as usize, temp);
    assert(a@.to_multiset() == old_a@.to_multiset());
}

proof fn lemma_sorted_segment_extended(a: &Vec<i32>, k: int)
    requires
        0 <= k < a.len(),
        sorted_seg(a, 0, k - 1),
        forall |l: int| 0 <= l < k ==> a[l as usize] <= a[k as usize],
    ensures
        sorted_seg(a, 0, k),
{
    assert forall|l: int, m: int| 0 <= l <= m <= k implies a[l as usize] <= a[m as usize] by {
        if m < k {
            assert(sorted_seg(a, 0, k - 1));
            assert(a[l as usize] <= a[m as usize]);
        } else if m == k {
            assert(0 <= l <= k);
            if l < k {
                assert(a[l as usize] <= a[k as usize]);
            } else { // l == k
                assert(a[l as usize] <= a[m as usize]); // a[k] <= a[k]
            }
        }
    }
}

proof fn lemma_multiset_pop_push(a: &mut Vec<i32>, idx: int, x: i32)
    requires
        0 <= idx <= a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
{
    let old_a_seq = old(a)@;
    a.insert(idx as usize, x);
    assert(a@.remove(idx) == old_a_seq);
    assert(a@.to_multiset() == old_a_seq.to_multiset().insert(x));
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(), //Add and prove this
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len(),
            sorted_seg(a, 0, i as int - 1),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let x = a[i];
        let mut j: usize = i;
        while j > 0 && a[j - 1] > x
            invariant
                0 <= j as int <= i as int,
                a@.to_multiset() == old(a).to_multiset(),
                (old(a)@.to_multiset()).insert(x) == a@.to_multiset().insert(a@[j as int - 1]),
                forall |k: int| j as int <= k < i as int ==> a[k as usize] >= x,
                forall |k: int| j as int + 1 <= k <= i as int ==> a[k as usize - 1] <= a[k as usize],
        {
            a.set(j, a[j - 1]);
            j = j - 1;
        }

        let old_a_seq = a@;
        a.insert(j, x);
        if j < i {
            let _ = a.remove(i + 1);
        } else {
            let _ = a.remove(i);
        }

        proof {
            lemma_sorted_segment_extended(a, i as int);
        }

        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}