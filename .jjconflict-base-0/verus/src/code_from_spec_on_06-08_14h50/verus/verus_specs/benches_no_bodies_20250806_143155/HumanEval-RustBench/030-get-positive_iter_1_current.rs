use vstd::prelude::*;

verus! {

fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            i <= input.len(),
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
    {
        if input[i] > 0 {
            result.push(input[i]);
        }
        i += 1;
    }
    
    result
}

}
fn main() {}