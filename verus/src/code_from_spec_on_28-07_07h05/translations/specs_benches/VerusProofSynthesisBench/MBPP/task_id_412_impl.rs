use vstd::prelude::*;

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    // post-conditions-start
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): updated loop structure to maintain invariant */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 4): added proof steps to maintain invariant with correct type casting */
        let old_i = i;
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
        
        // Prove that the invariant is maintained
        assert(arr@.subrange(0, i as int) == arr@.subrange(0, old_i as int).push(arr[old_i as int]));
        assert(result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0));
    }
    
    /* code modified by LLM (iteration 4): added assertion to prove postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!

fn main() {}