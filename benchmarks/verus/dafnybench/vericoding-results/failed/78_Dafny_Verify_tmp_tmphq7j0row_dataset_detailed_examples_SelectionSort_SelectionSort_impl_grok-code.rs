use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
use vstd::prelude::*;

verus! {

// Lemma to help with proving sortedness after swaps
#[verifier::spinoff_prover]
pub proof fn lemma_selection_sort_preserves_sort(sorted_prefix: int, a: Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < sorted_prefix ==> a@[i] <= a@[j],
        forall|i: int| 0 <= i < sorted_prefix ==> forall|j: int| sorted_prefix <= j < a.len() ==> a@[i] <= a@[j],
    ensures
        forall|i: int, j: int| 0 <= i < j <= sorted_prefix ==> a@[i] <= a@[j],
{
    assert forall |ii: int, jj: int| 0 <= ii < jj <= sorted_prefix implies a@[ii] <= a@[jj] by {
        if jj < sorted_prefix {
            // Use the require for prefix being sorted
        } else if jj == sorted_prefix {
            // ii < sorted_prefix, so a@[ii] <= a@[sorted_prefix]
        } else {
            // jj > sorted_prefix, but since jj <= sorted_prefix, impossible
        }
    };
}

} // end verus!
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        // Ensures the final array is sorted in ascending order
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        // Ensures that the final array has the same elements as the initial array
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i as int,
            i as int <= a.len() as int,
            a@.len() == old(a)@.len(),
            forall |k: int, l: int| 0 <= k < l < i as int ==> a@[k] <= a@[l],
            forall |k: int, l: int| i as int <= l < a@.len() ==> a@[k] <= a@[l],
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        // Find the index of the minimum in a[i..a.len()]
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < a.len()
            invariant
                i as int <= min_idx as int,
                min_idx as int < a.len() as int,
                i as int < j as int,
                j as int <= a.len() as int,
                forall |k: int| (i as int <= k < j as int) ==> a@[k as usize] >= a@[min_idx as usize],
                forall |k: int, l: int| 0 <= k < l < i as int ==> a@[k] <= a@[l],
                forall |k: int, l: int| i as int <= l < a@.len() ==> a@[k] <= a@[l],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }

        // Swap a[i] with a[min_idx]
        let temp = a[i];
        a[i] = a[min_idx];
        a[min_idx] = temp;

        // Assert that the prefix is now sorted up to i+1
        proof {
            lemma_selection_sort_preserves_sort(i as int, *a);
            assert(forall |k: int, l: int| 0 <= k < l <= i as int ==> a@[k] <= a@[l]);
            assert(forall |k: int, l: int| i as int < l < (i as int + 1) ==> a@[i as usize] <= a@[l as usize]);
            assert(forall |k: int, l: int| 0 <= k < i as int ==> i as int < l < a@.len() ==> a@[k] <= a@[l]);
        }

        i += 1;
    }
}
// </vc-code>

fn main() {
}

}