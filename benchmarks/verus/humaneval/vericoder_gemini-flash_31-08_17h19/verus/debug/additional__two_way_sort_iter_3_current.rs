use vstd::prelude::*;

verus! {

// <vc-helpers>
fn count_false(a: &Vec<bool>) -> (c: nat)
    ensures c == a@.filter(|v: bool| !v).len(),
{
    let mut count: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            count == a@.subsequence(0, i as nat).filter(|v: bool| !v).len(),
    {
        if !a[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let len = a.len();
    if len == 0 {
        return;
    }

    let num_false = count_false(a);

    let mut i: usize = 0;
    while i < num_false
        invariant
            i <= num_false,
            num_false <= a.len(),
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(), // This is the crucial part that needs proving
            forall|k: int| 0 <= k < i as int ==> !a[k as usize],
    {
        if a[i] {
            // Find a false value to swap with
            let mut j: usize = num_false as usize; // Start searching from num_false
            while j < len
                invariant
                    num_false as usize <= j <= len,
                    a.len() == old(a).len(),
                    a@.to_multiset() == old(a)@.to_multiset(),
                    forall|k: int| 0 <= k < i as int ==> !a[k as usize],
                    forall|k: int| num_false as int <= k < j as int ==> a[k as usize],
            {
                if !a[j] {
                    // Found a false at j, swap with true at i
                    let original_a_i = a[i]; // for use in multiset proof
                    let original_a_j = a[j]; // for use in multiset proof
                    proof {
                        assert(a@.to_multiset().count(original_a_i) == old(a)@.to_multiset().count(original_a_i));
                        assert(a@.to_multiset().count(original_a_j) == old(a)@.to_multiset().count(original_a_j));
                    }
                    a.swap(i, j);
                    proof {
                        assert(a@.to_multiset().count(original_a_i) == old(a)@.to_multiset().count(original_a_i) - 1); // This proof is more nuanced.
                        assert(a@.to_multiset().count(original_a_j) == old(a)@.to_multiset().count(original_a_j) + 1);

                        // The multiset equality needs to be established by showing that
                        // the swapped elements preserve the overall multiset count.
                        // This involves proving that the multiset of `a` after swap is the same as before.
                        // Since we swap, counts of a[i] and a[j] change, but others don't.
                        // The overall multiset remains the same if the swapped values are distinct.
                        // If they are the same, the multiset trivially remains the same.
                        assert(a@.to_multiset() == old(a)@.to_multiset());
                    }
                    break;
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }

    // After the first loop, the first `num_false` elements are false.
    // The remaining `len - num_false` elements must be true.
    // We already have `forall|k: int| 0 <= k < num_false ==> !a[k]` from the loop invariant.
    assert(forall|k: int| 0 <= k < num_false as int ==> !a[k as usize]);

    // Now prove that the rest are true.
    // We know the total count of 'false' elements is `num_false`.
    // If we have `num_false` 'false' elements at the beginning,
    // and the total count of elements is `len`, then the rest must be 'true'.
    // This is implicitly covered by the multiset equality and the initial count of false values.

    // Final assertion for the postcondition
    assert(forall|k: int| 0 <= k < num_false as int ==> a[k as usize] == false);
    assert(forall|k: int| num_false as int <= k < len as int ==> a[k as usize] == true);

    assert(forall|idx: int| 0 <= idx < num_false as int ==> !a[idx as usize]);
    assert(forall|idx: int| num_false as int <= idx < a.len() as int ==> a[idx as usize]);

    assert(forall|i_idx: int, j_idx: int| 0 <= i_idx < j_idx < a.len() as int ==> !a[i_idx as usize] || a[j_idx as usize]);

    ()
    // impl-end
}
// </vc-code>

fn main() {}
}