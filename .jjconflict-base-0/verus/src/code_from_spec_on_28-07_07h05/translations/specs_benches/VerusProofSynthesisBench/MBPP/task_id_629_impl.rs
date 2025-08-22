use vstd::prelude::*;

verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant to properly maintain the relationship */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 4): added proper reasoning about subrange extension and filtering */
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
            // When we extend the subrange by one element that is even,
            // the filtered result should include this new even element
            assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr@[i as int]));
            assert(arr@[i as int] % 2 == 0);
        } else {
            // When we extend the subrange by one element that is odd,
            // the filtered result should remain the same
            assert(arr@[i as int] % 2 != 0);
            assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr@[i as int]));
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): added final assertion to connect loop invariant to postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!

fn main() {}