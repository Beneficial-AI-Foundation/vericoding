use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(), //Add and prove this
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    proof {
        assert(sorted_seg(a, 0, 0));
    }
    if len > 1 {
        for i in 1..len
            invariant
                0 < i <= len,
                sorted_seg(a, 0, i - 1),
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            let mut j = i;
            while j > 0 && a@[j - 1] > a@[j]
                invariant
                    0 <= j <= i,
                    sorted_seg(a, 0, j - 1),
                    sorted_seg(a, j + 1, i),
                    forall|l: int, k: int| #![trigger sorted_seg(a, j + 1, i)] 0 <= l < k < j ==> a@[l] <= a@[k],
                    forall|l: int, k: int| #![trigger a@[l]] j < l <= k <= i ==> a@[l] <= a@[k],
                    a@.to_multiset() == old(a)@.to_multiset(),
            {
                a.swap(j - 1, j);
                proof {
                    assert(sorted_seg(a, 0, j - 1));
                    assert(a@.to_multiset() == old(a)@.to_multiset());
                }
                j = j - 1;
            }
            proof {
                assert(sorted_seg(a, 0, i));
                assert(a@.to_multiset() == old(a)@.to_multiset());
            }
        }
    }
    proof {
        assert(sorted_seg(a, 0, len - 1));
        assert(a@.to_multiset() == old(a)@.to_multiset());
    }
}
// </vc-code>

fn main() {}

}