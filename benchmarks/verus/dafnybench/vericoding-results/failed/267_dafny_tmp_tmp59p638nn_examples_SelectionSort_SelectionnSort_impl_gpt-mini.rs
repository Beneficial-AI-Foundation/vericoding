use vstd::prelude::*;

verus! {

// Two-state predicate for checking if multiset is preserved
spec fn preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

// Predicate for checking if array slice is ordered
spec fn ordered(a: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a.len()
{
    forall|i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// Two-state predicate for sorted array
spec fn sorted(a_old: Seq<i32>, a_new: Seq<i32>) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len() as nat) && preserved(a_old, a_new, 0, a_old.len() as nat)
}

// <vc-helpers>
use vstd::multiset::*;
use vstd::seq::*;
use vstd::vec::*;

spec fn seq_swap(s: Seq<i32>, i: nat, j: nat) -> Seq<i32>
    recommends i < s.len() && j < s.len()
{
    s.update(i as int, s[j as int]).update(j as int, s[i as int])
}

#[verifier(spec_public)]
proof fn seq_swap_preserves(s: Seq<i32>, i: nat, j: nat)
    requires i < s.len() && j < s.len()
    ensures seq_swap(s, i, j).to_multiset() == s.to_multiset()
{
    // For all elements x, counts are equal after swapping two positions.
    assert(forall |x: i32|
        #[trigger seq_swap(s, i, j).to_multiset(), s.to_multiset()]
        seq_swap(s, i, j).to_multiset().count(x) == s.to_multiset().count(x)
    );
    assert(seq_swap(s, i, j).to_multiset() == s.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    // In-place selection sort implementation that produces a sorted permutation of the original.
    let n: usize = a.len();
    // Save original sequence for later preservation proof
    let orig: Seq<i32> = a@;

    // Outer loop: for each position i, place the minimal remaining element at i.
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant a.len() == n
        invariant orig.len() == n as nat
        invariant a@.len() == n as nat
        invariant a@.to_multiset() == orig.to_multiset()
    {
        // find index of minimum in [i, n)
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant i <= min_idx && min_idx < n
            invariant i + 1 <= j && j <= n
            invariant a.len() == n
            invariant a@.to_multiset() == orig.to_multiset()
        {
            // compare a[j] and a[min_idx]
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }

        // swap a[i] and a[min_idx]
        if i != min_idx {
            // perform swap and use helper to show multiset preserved
            let old_seq: Seq<i32> = a@;
            a.swap(i as usize, min_idx as usize);
            proof {
                seq_swap_preserves(old_seq, i as nat, min_idx as nat);
            }
            assert(a@.to_multiset() == orig.to_multiset());
        }

        // To help verifier, assert length and multiset invariants explicitly.
        assert(a.len() == n);
        assert(a@.to_multiset() == orig.to_multiset());

        i = i + 1;
    }

    // Now a contains all elements; we need to prove it's ordered.
    if n >= 2 {
        let mut k: usize = 1;
        while k < n
            invariant 1 <= k && k <= n
            invariant a.len() == n
            invariant a@.to_multiset() == orig.to_multiset()
        {
            // Show a[k-1] <= a[k]
            assert(a[k - 1] <= a[k]);
            k = k + 1;
        }
    }

    // Final ensures: sorted(orig, a@)
    proof {
        assert(ordered(a@, 0, n as nat));
        assert(preserved(orig, a@, 0, n as nat));
    }
}
// </vc-code>

fn main() {
}

}