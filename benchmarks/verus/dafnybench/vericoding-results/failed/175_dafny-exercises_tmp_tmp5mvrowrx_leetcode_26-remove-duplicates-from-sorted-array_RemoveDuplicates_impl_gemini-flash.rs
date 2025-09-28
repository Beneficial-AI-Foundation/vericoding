use vstd::prelude::*;

verus! {

// <vc-helpers>
#[macro_export]
macro_rules! assert_seqs_equal {
    ($s1:expr, $s2:expr) => {
        // Requires s1 and s2 to be Seq<T> and T has the Eq trait
        assert!($s1.len() == $s2.len());
        assert!(
            forall(|i: int| { #[trigger($s1.index(i))] #[trigger($s2.index(i))]
                0 <= i && i < $s1.len() >>= $s1.index(i) == $s2.index(i)
            }),
        );
    };
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j],
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)@.contains(nums[i]),
        forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[i]),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let old_nums_vec = nums.clone(); // Capture the old state of nums as a Vec
    let old_nums_seq = Seq::<'_, i32>::new(nums.len(), |k: int| nums.deref()[k as usize]);

    if nums.len() == 0 {
        return 0;
    }

    // A ghost variable to track the sequence of the `nums` vector in each iteration
    // This is crucial for proving the properties about `nums`
    let mut nums_seq = old_nums_seq.clone();

    // Loop Invariant Proofs
    proof {
        assert_seqs_equal!(nums.view(), nums_seq);
    }

    #[verifier::loop_invariant]
    #[verifier::spec(
        // i and j are within bounds
        0 <= i && i <= j && j <= nums.len(),
        // The elements up to i are unique
        forall|k: int, l: int| 0 <= k < l < i ==> nums_seq.index(k) != nums_seq.index(l),
        // The elements up to i are from the original array and in order
        forall|k: int| 0 <= k < i ==> old_nums_seq.contains(nums_seq.index(k)),
        // All elements in the original sequence are either handled or still in the tail
        forall|k: int| 0 <= k < old_nums_seq.len() ==>
            (nums_seq.subrange(0, i as int).contains(old_nums_seq.index(k))) || (j < old_nums_seq.len() && #[trigger] old_nums_seq.subrange(j as int, old_nums_seq.len() as int).contains(old_nums_seq.index(k))),
        // The content of the vector matches the ghost sequence
        nums.view() == nums_seq,
        // The prefix of nums (up to i) is sorted and unique
        forall|k: int, l: int| 0 <= k < l < i ==> nums.view()[k] < nums.view()[l],
        // The elements from j to the end are the same as original from j
        forall|k: int| j <= k < nums.len() ==> old_nums_seq.index(k as int) == nums.view()[k],
        // The "processed" part of `nums` (up to `i`) contains unique, sorted elements
        // The elements `nums_seq[0..i]` are unique and monotonic
        forall |idx: int, idx2: int| 0 <= idx < idx2 < i ==> nums_seq[idx] < nums_seq[idx2],
        // All elements in `nums_seq[0..i]` are present in `old_nums_seq`
        forall |idx: int| 0 <= idx < i ==> old_nums_seq.contains(nums_seq[idx]),
        // The current `nums` vector content (up to `j`) is consistent with `nums_seq`
        forall |idx: int| 0 <= idx < j ==> nums.view()[idx] == nums_seq[idx],
    )]
    while j < nums.len()
    {
        if nums.deref()[j] != nums.deref()[i] {
            i = i + 1;
            nums.swap(i, j);
            proof {
                nums_seq = nums_seq.update(i as int, nums.before.view().index(j as int));
                nums_seq = nums_seq.update(j as int, nums.before.view().index(i as int));
            }
        }
        j = j + 1;

        // Maintain the invariant: nums.view() == nums_seq
        proof {
            assert_seqs_equal!(nums.view(), nums_seq);
        }
    }

    assert(nums.view() == nums_seq); // Final consistency check

    let num_length = (i + 1) as usize; // Cast to usize for return type

    // Proof for `0 <= num_length <= nums.len()`
    assert(0 <= num_length && num_length <= nums.len());

    // Proof for `forall|k: int, l: int| 0 <= k < l < num_length ==> nums[k] != nums[l]`
    proof {
        assert(forall|k: int, l: int| 0 <= k < l < num_length ==> nums_seq[k] != nums_seq[l]);
        assert(forall|k: int, l: int| 0 <= k < l < num_length ==> nums[k] != nums[l]);
    }

    // Proof for `forall|k: int| 0 <= k < num_length ==> old(nums)@.contains(nums[k])`
    proof {
        assert(forall|k: int| 0 <= k < num_length ==> old_nums_seq.contains(nums_seq[k]));
        assert(forall|k: int| 0 <= k < num_length ==> old_nums_seq.contains(nums[k]));
    }

    // Proof for `forall|k: int| 0 <= k < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[k])`
    proof {
        assert(forall |k: int| 0 <= k < old_nums_seq.len() ==> nums_seq.subrange(0, num_length as int).contains(old_nums_seq[k]));
        assert(forall |k: int| 0 <= k < old_nums_seq.len() ==> nums.view().subrange(0, num_length as int).contains(old_nums_seq[k]));
        assert(forall |k: int| 0 <= k < old_nums_seq.len() ==> nums.view().subrange(0, num_length as int).contains(old_nums_vec.view()[k]));
    }

    num_length
}
// </vc-code>

fn main() {
}

}