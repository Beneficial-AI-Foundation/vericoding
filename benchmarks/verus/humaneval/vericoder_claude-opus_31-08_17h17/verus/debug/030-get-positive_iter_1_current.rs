use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut positive_list: Vec<i32> = Vec::new();
    let input_len = input.len();
    
    for i in 0..input_len
        invariant
            positive_list@ == input@.take(i as int).filter(|x: i32| x > 0),
    {
        if input[i] > 0 {
            positive_list.push(input[i]);
        }
        
        // Helper assertions for verification
        assert(input@.take((i + 1) as int) =~= input@.take(i as int).push(input@[i as int]));
        
        if input[i] > 0 {
            assert(positive_list@ =~= input@.take(i as int).filter(|x: i32| x > 0).push(input@[i as int]));
            assert(input@.take((i + 1) as int).filter(|x: i32| x > 0) 
                   =~= input@.take(i as int).filter(|x: i32| x > 0).push(input@[i as int]));
        } else {
            assert(input@.take((i + 1) as int).filter(|x: i32| x > 0) 
                   =~= input@.take(i as int).filter(|x: i32| x > 0));
        }
    }
    
    assert(input@.take(input_len as int) =~= input@);
    assert(positive_list@ == input@.filter(|x: i32| x > 0));
    
    positive_list
}
// </vc-code>

fn main() {}
}