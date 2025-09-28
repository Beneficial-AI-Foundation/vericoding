use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
fn verus_vec_push<T>(vec: &mut Vec<T>, value: T)
    ensures
        vec.len() == old(vec.len()) + 1,
        vec.len() > 0,
        vec.content() == old(vec.content()).push(value),
{
    vec.push(value);
}
// </vc-helpers>

// <vc-spec>
fn filter_odd_numbers(arr: &[int]) -> (odd_list: Vec<int>)
    ensures 
        // All numbers in the output are odd and exist in the input 
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i]) && arr@.contains(odd_list[i]),
        // All odd numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_odd(arr[i]) ==> odd_list@.contains(arr[i]),
// </vc-spec>
// <vc-code>
{
    let mut odd_list: Vec<int> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            0 <= i as int,
            i as int <= arr.len() as int,
            forall|j: int| 0 <= j < odd_list.len() ==> is_odd(odd_list[j]) && arr@.contains(odd_list[j]),
            forall|j: int| 0 <= j < i as int && is_odd(arr[j]) ==> odd_list@.contains(arr[j]),
            forall|j: int| 0 <= j < odd_list.len() ==> {
                odd_list[j] == arr@[({
                    let mut found_idx_val: int = 0; // Use int for indices in ghost code
                        let old_i = i;
                        let mut k_ghost: int = 0;
                        while k_ghost < old_i as int
                            invariant
                                0 <= k_ghost <= old_i as int,
                                0 <= found_idx_val,
                                // found_idx_val < arr.len(), // This bound is not necessarily true unless found.
                                forall |l_ghost: int| 0 <= l_ghost < k_ghost ==> (arr@[l_ghost] != odd_list[j] || found_idx_val != l_ghost),
                        {
                            if arr@[k_ghost] == odd_list[j] {
                                found_idx_val = k_ghost;
                                break;
                            }
                            k_ghost = k_ghost + 1;
                        }
                    found_idx_val
                })]
            },
    {
        if is_odd(arr[i as int]) {
            let old_len = odd_list.len();
            verus_vec_push(&mut odd_list, arr[i as int]);
            assert(odd_list@.contains(arr[i as int]));
            assert(odd_list.len() == old_len + 1);
        }
        i = i + 1;
    }
    odd_list
}
// </vc-code>

fn main() {}

}