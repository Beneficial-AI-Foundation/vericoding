use vstd::prelude::*;

verus! {

//IMPL contains_consecutive_numbers
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
{
    let mut i = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            /* code modified by LLM (iteration 2): fixed invariant to properly track consecutive property */
            forall|k: int, l: int| 0 <= k < l < i + 1 && l == k + 1 ==> (arr[k] + 1 == arr[l]),
        decreases arr.len() - 1 - i,
    {
        /* code modified by LLM (iteration 2): added bounds assertions to help verification */
        assert(0 <= i < arr.len() - 1);
        assert(i + 1 < arr.len());
        assert(0 <= arr[i] + 1 < i32::MAX);
        
        if arr[i] + 1 != arr[i + 1] {
            /* code modified by LLM (iteration 2): added assertion to prove postcondition when returning false */
            assert(!(arr[i] + 1 == arr[i + 1]));
            assert(exists|k: int, l: int| 0 <= k < l < arr.len() && l == k + 1 && !(arr[k] + 1 == arr[l]));
            return false;
        }
        
        /* code modified by LLM (iteration 2): added assertion to help prove invariant preservation */
        assert(arr[i] + 1 == arr[i + 1]);
        
        i += 1;
        
        /* code modified by LLM (iteration 2): added assertion to prove invariant holds after increment */
        assert(forall|k: int, l: int| 0 <= k < l < i + 1 && l == k + 1 ==> (arr[k] + 1 == arr[l]));
    }
    
    /* code modified by LLM (iteration 2): added final assertion to prove postcondition when returning true */
    assert(i == arr.len() - 1);
    assert(forall|k: int, l: int| 0 <= k < l < arr.len() && l == k + 1 ==> (arr[k] + 1 == arr[l]));
    true
}

} // verus!

fn main() {}