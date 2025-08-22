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
    
    /* code modified by LLM (iteration 4): fixed loop invariant and added proper proof structure */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 4): fixed type issue by using arr@[i as int] instead of arr[i] */
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0).push(arr@[i as int]));
        } else {
            /* code modified by LLM (iteration 4): added assertion for odd case */
            assert(arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 == 0) == 
                   arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0));
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