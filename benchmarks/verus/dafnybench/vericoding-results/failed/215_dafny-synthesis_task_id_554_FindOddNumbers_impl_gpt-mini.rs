use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
// Helper lemmas for working with slices and sequences.

proof fn slice_index_in_seq(arr: &[i32], i: nat)
    requires i < arr.len()
    ensures arr@.contains(arr@[i])
{
    assert(arr@.contains(arr@[i]));
}
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &[i32]) -> (odd_list: Vec<i32>)
    // All numbers in the output are odd and exist in the input 
    ensures forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && arr@.contains(odd_list[i])
    // All odd numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> odd_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    let mut odd_list: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < arr.len()
        invariant i <= arr.len()
        invariant forall|j: nat| j < odd_list.len() ==> is_odd(odd_list[j] as int) && arr@.contains(odd_list[j])
        invariant forall|k: nat| k < i && is_odd(arr@[k] as int) ==> odd_list@.contains(arr@[k])
    {
        if is_odd(arr@[i] as int) {
            let old_len = odd_list.len();
            let old_seq = odd_list@;
            assert(forall|j: nat| j < old_len ==> is_odd(old_seq[j] as int) && arr@.contains(old_seq[j]));
            odd_list.push(arr@[i]);
            proof {
                assert(old_len + 1 == odd_list.len());
                assert(forall|j: nat| j < old_len ==> is_odd(odd_list[j] as int) && arr@.contains(odd_list[j]));
                assert(is_odd(arr@[i] as int));
                slice_index_in_seq(arr, i);
                assert(arr@.contains(arr@[i]));
            }
        }
        i += 1;
    }
    odd_list
}
// </vc-code>

fn main() {}

}