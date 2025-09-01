use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_subrange_filter_extend(s: Seq<i32>, i: int, x: i32)
    requires 
        0 <= i < s.len(),
        x == s[i],
    ensures 
        s.subrange(0, i + 1).filter(|y: i32| y > 0) == 
            if x > 0 { 
                s.subrange(0, i).filter(|y: i32| y > 0).push(x) 
            } else { 
                s.subrange(0, i).filter(|y: i32| y > 0) 
            }
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(s[i]));
    assert(sub_i_plus_1 == sub_i.push(x));
    
    if x > 0 {
        assert(sub_i_plus_1.filter(|y: i32| y > 0) == 
               sub_i.filter(|y: i32| y > 0).push(x)) by {
            assert(x > 0);
        };
    } else {
        assert(sub_i_plus_1.filter(|y: i32| y > 0) == 
               sub_i.filter(|y: i32| y > 0)) by {
            assert(!(x > 0));
        };
    }
}

proof fn lemma_subrange_full_equals_seq(s: Seq<i32>)
    ensures s.subrange(0, s.len() as int) == s
{
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
    
    for i in 0..input.len()
        invariant
            positive_list@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
    {
        if input[i] > 0 {
            positive_list.push(input[i]);
            proof {
                lemma_subrange_filter_extend(input@, i as int, input@[i as int]);
            }
        } else {
            proof {
                lemma_subrange_filter_extend(input@, i as int, input@[i as int]);
            }
        }
    }
    
    proof {
        lemma_subrange_full_equals_seq(input@);
        assert(input@.subrange(0, input.len() as int) == input@);
    }
    
    positive_list
}
// </vc-code>

fn main() {}
}