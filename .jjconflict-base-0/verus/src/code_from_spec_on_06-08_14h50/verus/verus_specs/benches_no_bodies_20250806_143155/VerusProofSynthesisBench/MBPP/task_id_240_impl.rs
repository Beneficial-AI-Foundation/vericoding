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
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for first loop */
    while i < first.len() - 1
        invariant
            i <= first.len() - 1,
            result@ == first@.subrange(0, i as int),
        decreases first.len() - 1 - i
    {
        result.push(first[i]);
        i += 1;
    }
    
    // Add all elements from second
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for second loop */
    while j < second.len()
        invariant
            j <= second.len(),
            result@ == first@.subrange(0, first.len() - 1).add(second@.subrange(0, j as int)),
        decreases second.len() - j
    {
        result.push(second[j]);
        j += 1;
    }
    
    result
}

} // verus!


fn main() {}