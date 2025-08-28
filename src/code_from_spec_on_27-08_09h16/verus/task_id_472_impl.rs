use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn consecutive_up_to(arr: &Vec<i32>, bound: int) -> bool {
    forall|k: int, l: int| 0 <= k < l < bound && l == k + 1 ==> arr[k] + 1 == arr[l]
}
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    if arr.len() == 1 {
        return true;
    }
    
    let mut i = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            consecutive_up_to(arr, i + 1),
        decreases arr.len() - 1 - i,
    {
        let arr_i = arr[i];
        let arr_i_plus_1 = arr[i + 1];
        
        if arr_i + 1 != arr_i_plus_1 {
            proof {
                assert(0 <= i < i + 1 < arr.len() && i + 1 == i + 1);
                assert(!(arr[i as int] + 1 == arr[(i + 1) as int]));
                assert(exists|x: int, y: int| 0 <= x < y < arr.len() && y == x + 1 && !(arr[x] + 1 == arr[y]));
            }
            return false;
        }
        
        i += 1;
        
        proof {
            assert(consecutive_up_to(arr, i + 1));
        }
    }
    
    proof {
        assert(i == arr.len() - 1);
        assert(consecutive_up_to(arr, arr.len()));
        assert(forall|k: int, l: int| 0 <= k < l < arr.len() && l == k + 1 ==> arr[k] + 1 == arr[l]);
    }
    
    true
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}