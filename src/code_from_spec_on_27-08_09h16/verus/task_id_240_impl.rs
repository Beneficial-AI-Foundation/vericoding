use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)
    // pre-conditions-start
    requires
        first.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    // Copy all elements except the last one from first
    for i in 0..first.len() - 1
        invariant
            result.len() == i,
            result@.len() == i,
            result@ == first@.subrange(0, i as int),
            i < first.len(),
    {
        result.push(first[i]);
    }
    
    // Add all elements from second
    for i in 0..second.len()
        invariant
            result.len() == (first.len() - 1) + i,
            result@.len() == (first.len() - 1) + i,
            result@ == first@.subrange(0, first.len() as int - 1).add(second@.subrange(0, i as int)),
            i <= second.len(),
    {
        result.push(second[i]);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}