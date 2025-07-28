use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut result = Vec::new();
    
    /* code modified by LLM (iteration 1): Fixed loop bounds and invariant to ensure proper subrange bounds */
    // Add all elements from first except the last one
    for i in 0..(first.len() - 1)
        invariant
            i <= first.len() - 1,
            result@ == first@.subrange(0, i as int),
    {
        /* code modified by LLM (iteration 1): Access is safe due to loop bound and invariant */
        result.push(first[i]);
    }
    
    /* code modified by LLM (iteration 1): Fixed invariant to ensure proper subrange bounds for second vector */
    // Add all elements from second
    for i in 0..second.len()
        invariant
            i <= second.len(),
            result@ == first@.subrange(0, (first.len() - 1) as int).add(second@.subrange(0, i as int)),
    {
        /* code modified by LLM (iteration 1): Access is safe due to loop bound */
        result.push(second[i]);
    }
    
    result
}

} // verus!