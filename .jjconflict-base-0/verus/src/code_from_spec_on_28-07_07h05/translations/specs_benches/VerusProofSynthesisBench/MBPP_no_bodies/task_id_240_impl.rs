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
    /* code modified by LLM (iteration 1): fixed loop bounds and invariant to handle edge case when first.len() == 1 */
    for i in 0..(first.len() - 1)
        invariant
            i <= first.len() - 1,
            result@ == first@.subrange(0, i as int),
    {
        /* code modified by LLM (iteration 1): added bounds assertion for array access */
        assert(i < first.len());
        result.push(first[i]);
    }
    
    // Add all elements from second
    /* code modified by LLM (iteration 1): fixed invariant to properly handle subrange bounds */
    for i in 0..second.len()
        invariant
            i <= second.len(),
            result@ == first@.subrange(0, (first.len() - 1) as int).add(second@.subrange(0, i as int)),
    {
        /* code modified by LLM (iteration 1): added bounds assertion for array access */
        assert(i < second.len());
        result.push(second[i]);
    }
    
    result
}

} // verus!

fn main() {}