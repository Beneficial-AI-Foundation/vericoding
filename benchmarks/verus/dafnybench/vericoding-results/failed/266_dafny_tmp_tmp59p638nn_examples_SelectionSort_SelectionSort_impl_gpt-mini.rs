use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
// <vc-helpers>
// No helpers needed for this proof.
proof fn int_index_nonneg_to_usize(i: int) -> (usize)
    ensures i >= 0 ==> (i as usize) >= 0
{
    // trivial helper to ensure uses of `as usize` are well-formed in proofs
    if i >= 0 {
        let _u: usize = i as usize;
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    proof {
        // capture original multiset for use in invariants
        let orig: Seq<int> = a@;
        let mut i: int = 0;
        while i < n
            invariant 0 <= i <= n;
            invariant ordered(a@, 0, i);
            invariant forall |k: int, l: int| 0 <= k < i && i <= l < n ==> a@[k] <= a@[l];
            invariant a.len() == orig.len();
            invariant a@.to_multiset() =~= orig.to_multiset();
        {
            // find index of minimum element in [i, n)
            let mut m: int = i;
            let mut j: int = i + 1;
            while j < n
                invariant i + 1 <= j <= n;
                invariant i <= m < j;
                invariant forall |k: int| i <= k < j ==> a@[m] <= a@[k];
            {
                // runtime reads; safe because indices are in-bounds by invariants
                if a[j as usize] < a[m as usize] {
                    m = j;
                }
                j += 1;
            }

            // capture sequence before swap to help reasoning
            let s_pre: Seq<int> = a@;

            // swap a[i] and a[m]
            a.swap(i as usize, m as usize);

            // After swap, show new prefix ordered and prefix<=suffix properties hold.
            // First, handle the ordered property for the newly extended prefix [0, i+1)
            {
                // For all t with 0 < t < i+1, show a[t-1] <= a[t]
                assert({
                    forall |t: int| 0 < t && t < i+1 ==>
                        a@[t-1] <= a@[t]
                });
            }

            // Next, show prefix<=suffix holds for new i+1
            {
                assert({
                    forall |k: int, l: int| 0 <= k < i+1 && i+1 <= l < n ==>
                        a@[k] <= a@[l]
                });
            }

            // Finally, show multiset preserved after swap.
            // Vec::swap preserves the multiset of elements, so invariant holds.
            assert(a@.to_multiset() =~= orig.to_multiset());

            i += 1;
        }

        // At loop end i == n, so ordered(a@, 0, n) holds by invariant
        assert(ordered(a@, 0, n));
        assert(a.len() == orig.len());
        assert(a@.to_multiset() =~= orig.to_multiset());
    }
}
// </vc-code>

fn main() {}

}