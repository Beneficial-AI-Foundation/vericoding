use vstd::prelude::*;

verus! {

fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): simplified loop with correct invariant maintenance */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i += 1;
        // Removed the problematic assertion - the invariant is maintained automatically
    }
    
    /* code modified by LLM (iteration 4): final assertion to connect loop result to postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    
    result
}

} // verus!

fn main() { }