use vstd::prelude::*;


verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let mut result = true;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result ==> forall|j: int| 0 <= j < i ==> ((j % 2) == (arr@[j] % 2)),
        decreases arr.len() - i
    {
        if (i % 2) != (arr@[i] % 2) {
            result = false;
            break;
        }
        i = i + 1;
    }
    
    // If loop completes with result still true, check all indices
    if result {
        proof {
            assert(forall|j: int| 0 <= j < arr.len() ==> ((j % 2) == (arr@[j] % 2)));
        }
    } else {
        proof {
            // If result is false, there exists some index where condition fails
            assert(exists|j: int| 0 <= j < arr.len() && ((j % 2) != (arr@[j] % 2)));
        }
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}