use vstd::prelude::*;

fn main() {}

verus! {

//IMPL replace_last_element
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut result = Vec::new();
    
    // Add all elements from first except the last one
    /* code modified by LLM (iteration 1): Fixed loop bounds and invariant to handle the case when first.len() == 1 */
    for i in 0..(first.len() - 1)
        invariant
            i <= first.len() - 1,
            result@ == first@.subrange(0, i as int),
    {
        /* code modified by LLM (iteration 1): Added bounds check assertion before indexing */
        assert(i < first.len() - 1);
        assert(i < first.len());
        result.push(first[i]);
    }
    
    // Add all elements from second
    /* code modified by LLM (iteration 1): Fixed invariant to avoid subrange precondition issues when second is empty */
    for i in 0..second.len()
        invariant
            i <= second.len(),
            result@ == first@.subrange(0, first.len() - 1).add(second@.subrange(0, i as int)),
    {
        /* code modified by LLM (iteration 1): Added bounds check assertion before indexing */
        assert(i < second.len());
        result.push(second[i]);
    }
    
    result
}

} // verus!