use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers required for this proof.
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n: nat = a@.len();
    let old_ms = a@.to_multiset();

    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            // prefix 0..i is sorted
            forall |p: nat, q: nat| p < q && q < i ==> a@[p] <= a@[q],
            // every element in prefix <= every element in suffix
            forall |p: nat, q: nat| p < i && i <= q && q < n ==> a@[p] <= a@[q],
            // multiset preserved
            a@.to_multiset() == old_ms,
    {
        // find minimum index m in [i, n)
        let mut m: nat = i;
        let mut j: nat = if i + 1 <= n { i + 1 } else { n };
        while j < n
            invariant
                i <= m && m < n,
                i + 1 <= j && j <= n,
                // m is minimal in a[i..j)
                forall |k: nat| i <= k && k < j ==> a@[m] <= a@[k],
                // multiset preserved
                a@.to_multiset() == old_ms,
        {
            if a@[j] < a@[m] {
                m = j;
            }
            j = j + 1;
        }

        // capture sequence before swap to reason about values
        let seq_before = a@;

        // from inner loop invariant when j == n, m is minimal over i..n
        assert(forall |k: nat| i <= k && k < n ==> seq_before@[m] <= seq_before@[k]);

        // also from outer invariant prior to swap: every prefix element <= every suffix element (including m)
        assert(forall |p: nat| p < i ==> seq_before@[p] <= seq_before@[m]);

        // perform swap placing minimum at position i
        a.swap(i, m);

        // Prove new prefix 0..i+1 is sorted:
        assert(forall |p: nat, q: nat|
            p < q && q < i + 1 ==>
            {
                if q < i {
                    a@[p] <= a@[q]
                } else {
                    // q == i, so p < i
                    a@[p] <= a@[q]
                }
            }
        );

        // Prove prefix <= suffix for next iteration: for all p in 0..i+1 and q in i+1..n, a[p] <= a[q]
        assert(forall |p: nat, q: nat|
            p < i + 1 && i + 1 <= q && q < n ==>
            {
                if p < i {
                    a@[p] <= a@[q]
                } else {
                    // p == i
                    a@[p] <= a@[q]
                }
            }
        );

        // multiset preserved after swap (Vec::swap is specified to preserve multiset)
        assert(a@.to_multiset() == old_ms);

        i = i + 1;
    }

    // At loop exit i == n, so prefix 0..n is sorted, i.e., whole array sorted
    assert(forall |p: nat, q: nat| p < q && q < n ==> a@[p] <= a@[q]);
    assert(a@.to_multiset() == old_ms);
}
// </vc-code>

fn main() {}

}