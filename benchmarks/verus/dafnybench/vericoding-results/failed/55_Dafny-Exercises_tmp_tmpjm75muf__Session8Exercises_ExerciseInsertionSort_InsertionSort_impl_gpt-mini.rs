use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
proof fn noop_helper() {
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
    let n: int = a.len() as int;
    let old_ms = a@.to_multiset();

    let mut k: int = 0;
    while (k < n)
        invariant 0 <= k && k <= n;
        invariant a.len() as int == n;
        invariant a@.to_multiset() == old_ms;
        invariant sorted_seg(a, 0, k - 1);
        invariant forall|i: int, j: int| 0 <= i && i < k && k <= j && j < n ==> a@[i] <= a@[j];
    {
        // find index m of minimum element in [k, n)
        let mut m: int = k;
        let mut i: int = k + 1;
        while (i < n)
            invariant (k < n) ==> (k <= m && m < n);
            invariant k <= i && i <= n;
            invariant a.len() as int == n;
            invariant a@.to_multiset() == old_ms;
            invariant sorted_seg(a, 0, k - 1);
            invariant forall|t: int| k <= t && t < i ==> a@[m] <= a@[t];
            invariant forall|p: int, q: int| 0 <= p && p < k && k <= q && q < n ==> a@[p] <= a@[q];
        {
            if a@[i] < a@[m] {
                m = i;
            }
            i += 1;
        }

        // swap minimal element into position k
        if m != k {
            a.swap(k as usize, m as usize);
        }

        // Establish that prefix up to k is sorted (i.e., for all i<j<=k, a[i] <= a[j])
        {
            assert(forall|i: int, j: int|
                0 <= i && i < j && j <= k ==> a@[i] <= a@[j]);
        }

        // Maintain that every prefix element <= every suffix element for next iteration
        {
            assert(forall|i: int, j: int|
                0 <= i && i < (k + 1) && (k + 1) <= j && j < n ==> a@[i] <= a@[j]);
        }

        k += 1;
    }

    // Final assertions to match ensures
    assert(a.len() as int == n);
    assert(a@.to_multiset() == old_ms);
    if n == 0 {
        // vacuously sorted
    } else {
        assert(sorted_seg(a, 0, n - 1));
    }
}
// </vc-code>

fn main() {}

}