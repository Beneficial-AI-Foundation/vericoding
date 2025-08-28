use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
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
    // Create a new vector with elements from 'first' except the last one
    let mut result = Vec::new();
    let len = first.len();
    
    let mut i = 0;
    while i < len - 1
        invariant
            i <= len - 1,
            result@ == first@.subrange(0, i as int),
        decreases len - 1 - i
    {
        result.push(first@[i as int]);
        i = i + 1;
    }
    
    // Append all elements from 'second'
    let mut j = 0;
    let second_len = second.len();
    while j < second_len
        invariant
            j <= second_len,
            i == len - 1,
            result@ == first@.subrange(0, i as int).add(second@.subrange(0, j as int)),
        decreases second_len - j
    {
        result.push(second@[j as int]);
        j = j + 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}