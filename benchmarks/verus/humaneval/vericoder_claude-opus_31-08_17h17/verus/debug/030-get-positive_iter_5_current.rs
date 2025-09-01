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
    
    let mut i: usize = 0;
    while i < input_len
        invariant
            i <= input_len,
            positive_list@ == input@.take(i as int).filter(|x: i32| x > 0),
    {
        let elem = input[i as int];
        if elem > 0i32 {
            positive_list.push(elem);
        }
        
        proof {
            // Prove that taking i+1 elements is taking i elements plus one more
            assert(input@.take((i + 1) as int) =~= input@.take(i as int).push(input@[i as int]));
            
            // Prove the invariant is maintained
            if elem > 0i32 {
                // When we add a positive element, the filter includes it
                assert(input@.take((i + 1) as int).filter(|x: i32| x > 0) 
                       =~= input@.take(i as int).filter(|x: i32| x > 0).push(input@[i as int]));
            } else {
                // When the element is not positive, the filter remains the same
                assert(input@.take((i + 1) as int).filter(|x: i32| x > 0) 
                       =~= input@.take(i as int).filter(|x: i32| x > 0));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        // Final proof that taking all elements gives us the full sequence
        assert(input@.take(input_len as int) =~= input@);
    }
    
    positive_list
}
// </vc-code>

fn main() {}
}