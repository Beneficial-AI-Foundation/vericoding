use vstd::prelude::*;

fn main() {}

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant maintenance with proper proof annotations */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        if arr[i] < 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 4): fixed type mismatch by casting arr[i] to int */
            assert(arr@.subrange(0, i as int + 1).filter(|x: i32| x < 0) == 
                   arr@.subrange(0, i as int).filter(|x: i32| x < 0).push(arr[i] as int));
        } else {
            /* code modified by LLM (iteration 4): prove that skipping non-negative element maintains invariant */
            assert(arr@.subrange(0, i as int + 1).filter(|x: i32| x < 0) == 
                   arr@.subrange(0, i as int).filter(|x: i32| x < 0));
        }
        i += 1;
        
        /* code modified by LLM (iteration 4): simplified assertion using subrange property */
        assert(result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0));
    }
    
    /* code modified by LLM (iteration 4): added assertion to help prove postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!