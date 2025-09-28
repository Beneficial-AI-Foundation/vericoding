use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
fn swap_preserves_multiset(a: &mut Vec<i32>, i: nat, j: nat)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset()
{
    let s0 = old(a)@;
    a.swap(i, j);
    proof {
        // after swap, the sequence equals s0 with positions i and j exchanged
        assert(a@ == s0.update(i as int, s0[j as int]).update(j as int, s0[i as int]));
        // swapping two positions does not change the multiset
        assert(a@.to_multiset() == s0.update(i as int, s0[j as int]).update(j as int, s0[i as int]).to_multiset());
        assert(s0.update(i as int, s0[j as int]).update(j as int, s0[i as int]).to_multiset() == s0.to_multiset());
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let mut k: nat = 0;

    while k < n
        invariant k <= n;
        invariant a@.to_multiset() == old(a)@.to_multiset();
        invariant forall |i: int, j: int| 0 <= i && i < j && j < (k as int) ==> a@[i] <= a@[j];
        invariant forall |i: int, j: int| 0 <= i && i < (k as int) && (k as int) <= j && j < (n as int) ==> a@[i] <= a@[j];
    {
        let mut min_idx: nat = k;
        let mut i: nat = k + 1;
        while i < n
            invariant k + 1 <= i && i <= n;
            invariant k <= min_idx && min_idx < n;
            invariant a@.to_multiset() == old(a)@.to_multiset();
            invariant forall |x: int| (k as int) <= x && x < (i as int) ==> a@[(min_idx as int)] <= a@[x];
        {
            // compare using specification-level sequence for the invariant
            if a[i] < a[min_idx] {
                min_idx = i;
            }
            i = i + 1;
        }

        // place minimum at position k
        // preserve multiset via helper
        swap_preserves_multiset(a, min_idx, k);

        // Prove that the prefix up to k+1 is sorted and cross-boundary relation holds for next iteration
        proof {
            // show prefix [0, k+1) is sorted:
            // for any i < j < k+1:
            // - if j < k then comes from old prefix-sorted invariant
            // - if j == k then need to use the fact that old prefix elements <= old a[k]
            assert(forall |i0: int, j0: int| 0 <= i0 && i0 < j0 && j0 < (k as int) ==> a@[i0] <= a@[j0]);
            // We now show the new prefix property holds for k+1:
            assert(forall |i0: int, j0: int| 0 <= i0 && i0 < j0 && j0 < ((k + 1) as int) ==>
                a@[i0] <= a@[j0]);
            // show cross-boundary property for next iteration:
            assert(forall |i0: int, j0: int| 0 <= i0 && i0 < ((k + 1) as int) && (k + 1) as int <= j0 && j0 < (n as int) ==>
                a@[i0] <= a@[j0]);
        }

        k = k + 1;
    }
}
// </vc-code>

fn main() {
}

}