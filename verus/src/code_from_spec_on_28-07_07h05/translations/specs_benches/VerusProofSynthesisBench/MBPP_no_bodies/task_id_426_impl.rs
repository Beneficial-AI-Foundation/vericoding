use vstd::prelude::*;

verus! {

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    // post-conditions-start
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): fixed invariant maintenance by adding assertions */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 3): added assertions to prove invariant maintenance with proper type casting */
        let old_i = i;
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i += 1;
        
        /* code modified by LLM (iteration 3): prove that invariant is maintained with correct type casting */
        assert(arr@.subrange(0, old_i as int) =~= arr@.subrange(0, i as int).drop_last());
        assert(arr@.subrange(0, i as int) =~= arr@.subrange(0, old_i as int).push(arr[old_i as int]));
    }
    
    /* code modified by LLM (iteration 3): added assertion to prove postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) =~= arr@);
    
    result
}

} // verus!

fn main() {}