use vstd::prelude::*;

verus! {

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    // pre-conditions-start
    requires
        first.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
    // post-conditions-end
{
    let mut result = Vec::new();
    
    // Add all elements from first except the last one
    for i in 0..(first.len() - 1)
        invariant
            /* code modified by LLM (iteration 1): Added bounds check for subrange and loop index */
            i <= first.len() - 1,
            result@ == first@.subrange(0, i as int),
    {
        /* code modified by LLM (iteration 1): Access is now safe due to loop bounds */
        result.push(first[i]);
    }
    
    // Add all elements from second
    for i in 0..second.len()
        invariant
            /* code modified by LLM (iteration 1): Added bounds check and fixed subrange precondition */
            i <= second.len(),
            result@ == first@.subrange(0, first.len() - 1).add(second@.subrange(0, i as int)),
    {
        result.push(second[i]);
    }
    
    result
}

} // verus!

fn main() {}