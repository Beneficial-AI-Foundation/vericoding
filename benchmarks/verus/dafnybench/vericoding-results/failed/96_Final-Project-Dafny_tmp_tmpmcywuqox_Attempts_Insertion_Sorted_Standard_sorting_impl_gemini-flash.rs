use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
fn insertion_sort_core(array: &mut Vec<int>, left_idx: int, right_idx: int)
    requires
        0 <= left_idx <= right_idx <= array.len(),
    ensures
        insertion_sorted(array@, left_idx, right_idx),
        array@.len() == old(array).len(),
        forall|i: int| (0 <= i < array.len() && !(left_idx <= i < right_idx)) ==> array@[i] == old(array)@[i],
{
    let n = right_idx;
    let start = left_idx + 1;

    #[verifier::loop_invariant(
        left_idx <= i && i <= n, // Corrected upper bound for i
        insertion_sorted(array@, left_idx, i),
        array@.len() == old(array).len(),
        forall|j: int| (0 <= j < array.len() && !(left_idx <= j < i)) ==> array@[j] == old(array)@[j],
    )]
    for i in start..n {
        let key = array@[i];
        let mut j: int = i - 1;

        #[verifier::loop_invariant(
            left_idx <= i,
            j >= left_idx - 1,
            j < i,
            array@.len() == old(array).len(),
            forall|k: int| #[trigger] (j < k && k < i) ==> array@[k] > key && array@[k] == old(array)@[k+1],
            // Add the following invariant to track the elements that are shifted
            forall|k: int| (left_idx <= k <= j) ==> array@[k] == old(array)@[k],
            array@[i] == old(array)@[i], // The key element is preserved
        )]
        while j >= left_idx && array@[j] > key {
            array.swap(j as usize, (j + 1) as usize);
            j = j - 1;
        }

        // Prove that the element at j+1 is now 'key' and other elements are sorted
        proof {
            if j + 1 != i {
                // Assert sorted property around the inserted element
                assert(insertion_sorted(array@, left_idx, j+1));
                assert(insertion_sorted(array@, j+2, i+1));
                assert(array@[j+1] == key);
                if j+1 > left_idx && array@[j] > array@[j+1] {
                    assert(false); // This should not happen if the loop terminated correctly
                }
            }
            assert(insertion_sorted(array@, left_idx, i + 1));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let n_len = array.len();

    if n_len <= 1 {
        // Already sorted or empty, satisfies the ensures clause trivially.
        return;
    }

    insertion_sort_core(array, 0, n_len as int);
}
// </vc-code>

fn main() {}

}