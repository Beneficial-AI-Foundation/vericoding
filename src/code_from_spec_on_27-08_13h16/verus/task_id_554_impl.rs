use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            result@.len() <= arr@.len(),
            forall|k: int| 0 <= k < result@.len() ==> result@[k] % 2 != 0,
            forall|k: int| 0 <= k < i ==> (arr@[k] % 2 != 0 ==> exists|j: int| 0 <= j < result@.len() && result@[j] == arr@[k]),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i = i + 1;
    }

    proof {
        assert_seqs_equal!(result@, arr@.filter(|x: u32| x % 2 != 0));
    }

    result
}
// </vc-code>

} // verus!

fn main() { }