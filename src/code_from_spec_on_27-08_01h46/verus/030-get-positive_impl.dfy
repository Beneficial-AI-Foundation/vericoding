use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn filter_subrange_property<T>(s: Seq<T>, start: int, end: int, pred: spec_fn(T) -> bool) -> bool {
    s.subrange(start, end).filter(pred) == s.filter(pred).subrange(start, s.filter(pred).len().min(end - start) as nat)
}
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
    let mut positive_list = Vec::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            i <= input.len(),
            positive_list@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i,
    {
        if input[i as int] > 0 {
            positive_list.push(input[i as int]);
            proof {
                let old_i = i as int;
                let new_i = (i + 1) as int;
                assert(input@.subrange(0, new_i) == input@.subrange(0, old_i).push(input[i as int]));
                assert(input[i as int] > 0);
                assert(input@.subrange(0, new_i).filter(|x: i32| x > 0) == 
                       input@.subrange(0, old_i).filter(|x: i32| x > 0).push(input[i as int]));
            }
        } else {
            proof {
                let old_i = i as int;
                let new_i = (i + 1) as int;
                assert(input@.subrange(0, new_i) == input@.subrange(0, old_i).push(input[i as int]));
                assert(input[i as int] <= 0);
                assert(input@.subrange(0, new_i).filter(|x: i32| x > 0) == 
                       input@.subrange(0, old_i).filter(|x: i32| x > 0));
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(i == input.len());
        assert(input@.subrange(0, i as int) == input@);
    }
    
    positive_list
}
// </vc-code>

}
fn main() {}