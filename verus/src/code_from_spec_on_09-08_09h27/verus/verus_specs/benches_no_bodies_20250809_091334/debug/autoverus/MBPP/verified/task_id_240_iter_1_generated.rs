use vstd::prelude::*;

fn main() {
}

verus! {

fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    requires
        first.len() > 0,
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
{
    let mut result = Vec::new();
    
    // Add all elements from first except the last one
    for i in 0..(first.len() - 1)
        invariant
            result@ == first@.subrange(0, i as int),
    {
        result.push(first[i]);
    }
    
    // Add all elements from second
    for i in 0..second.len()
        invariant
            result@ == first@.subrange(0, first.len() - 1).add(second@.subrange(0, i as int)),
    {
        result.push(second[i]);
    }
    
    result
}

} // verus!