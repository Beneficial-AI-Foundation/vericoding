use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

proof fn lemma_sorted_seg_smaller(a: &Vec<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= k <= j + 1 <= a.len(),
        sorted_seg(a, i, j),
    ensures
        sorted_seg(a, i, k),
{
}

proof fn lemma_sorted_seg_larger(a: &Vec<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k + 1 <= a.len(),
        sorted_seg(a, i, j),
        sorted_seg(a, j, k),
    ensures
        sorted_seg(a, i, k),
{
    assert forall|l: int, m: int| i <= l <= m <= k implies a[l] <= a[m] by {
        if l < j && m > j {
            assert(a[l] <= a[j]);
            assert(a[j] <= a[m]);
        }
    };
}

proof fn lemma_multiset_insert(a: &Vec<i32>, i: int, value: i32, old_a: Seq<i32>)
    requires
        0 <= i <= a.len(),
        a@ == old_a.insert(i, value),
    ensures
        a@.to_multiset() == old_a.to_multiset().insert(value),
{
}

proof fn lemma_multiset_remove(a: &Vec<i32>, i: int, old_a: Seq<i32>)
    requires
        0 <= i < a.len(),
        old_a == a@.remove(i),
    ensures
        old_a.to_multiset() == a@.to_multiset().remove(a@[i]),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(), //Add and prove this
// </vc-spec>
// </vc-spec>

// <vc-code>
fn insertion_sort(a: &mut Vec<i32>)
    ensures
        sorted_seg(a, 0, (a.len() as int) - 1),
        a@.to_multiset() == old(a)@.to_multiset(),
{
    if a.len() <= 1 {
        return;
    }

    let mut i: usize = 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sorted_seg(a, 0, (i as int) - 1),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let key = a[i];
        let mut j: int = (i as int) - 1;
        while j >= 0 && a[j as usize] > key
            invariant
                0 <= i < a.len(),
                -1 <= j < i as int,
                sorted_seg(a, 0, (i as int) - 1),
                forall|k: int| j < k <= i as int - 1 ==> a[k as usize] > key,
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            a[(j + 1) as usize] = a[j as usize];
            j = j - 1;
        }
        a[(j + 1) as usize] = key;
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}