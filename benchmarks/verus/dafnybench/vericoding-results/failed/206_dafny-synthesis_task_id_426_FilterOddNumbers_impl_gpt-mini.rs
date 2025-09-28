use vstd::prelude::*;

verus! {

/**
 * Filter odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
// No helpers needed for this verification
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
    let mut res: Vec<int> = Vec::new();
    let mut i: nat = 0;
    while i < arr.len()
        decreases arr.len() - i;
        invariant 0 <= i && i <= arr.len();
        invariant forall|k: int| (0 <= k && k < i) ==> (is_odd(arr[k]) ==> res@.contains(arr[k]));
        invariant forall|j: int| 0 <= j && j < res.len() ==> is_odd(res[j]) && arr@.contains(res[j]);
    {
        let v: int = arr[i];
        if is_odd(v) {
            let old_res_seq: Seq<int> = res@;
            let old_len: nat = res.len();
            proof {
                assert(forall|j: int| 0 <= j && j < old_len ==> is_odd(old_res_seq[j]) && arr@.contains(old_res_seq[j]));
                assert(forall|k: int| (0 <= k && k < i) ==> (is_odd(arr[k]) ==> old_res_seq.contains(arr[k])));
            }
            res.push(v);
            proof {
                assert(res.len() == old_len + 1);
                assert(forall|j: int| 0 <= j && j < old_len ==> res[j] == old_res_seq[j]);
                assert(res[old_len] == v);
                // elements before old_len remain odd and from arr
                assert(forall|j: int| 0 <= j && j < old_len ==> is_odd(res[j]) && arr@.contains(res[j]));
                // new element is odd and from arr
                assert(is_odd(res[old_len]) && arr@.contains(res[old_len]));
                // combine to get the full property for res
                assert(forall|j: int| 0 <= j && j < res.len() ==> is_odd(res[j]) && arr@.contains(res[j]));
            }
            proof {
                // update the invariant relating processed prefix to res membership
                // for k < i the property held for old_res_seq and old elements are preserved in res
                assert(forall|k: int| (0 <= k && k < i) ==> (is_odd(arr[k]) ==> old_res_seq.contains(arr[k])));
                assert(forall|k: int| (0 <= k && k < i) ==> (is_odd(arr[k]) ==> res@.contains(arr[k])));
                // for k == i, if arr[i] is odd then we just pushed it
                assert(is_odd(arr[i]) ==> res@.contains(arr[i]));
                // combine for k < i+1
                assert(forall|k: int| (0 <= k && k < i+1) ==> (is_odd(arr[k]) ==> res@.contains(arr[k])));
            }
        }
        i = i + 1;
    }
    proof {
        // From the loop invariants when i == arr.len(), we get both postconditions.
        assert(i == arr.len());
        assert(forall|j: int| 0 <= j && j < res.len() ==> is_odd(res[j]) && arr@.contains(res[j]));
        assert(forall|k: int| (0 <= k && k < arr.len()) ==> (is_odd(arr[k]) ==> res@.contains(arr[k])));
    }
    res
}
// </vc-code>

fn main() {}

}