use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 4): added helper lemma to prove filter properties */
proof fn lemma_filter_subrange_extend(input: Seq<i32>, i: int)
    requires 0 <= i < input.len()
    ensures 
        input.subrange(0, i + 1).filter(|x: i32| x > 0) == 
        if input[i] > 0 {
            input.subrange(0, i).filter(|x: i32| x > 0).push(input[i])
        } else {
            input.subrange(0, i).filter(|x: i32| x > 0)
        }
{
    let sub_i = input.subrange(0, i);
    let sub_i_plus_1 = input.subrange(0, i + 1);
    
    assert(sub_i_plus_1 == sub_i.push(input[i]));
    
    if input[i] > 0 {
        assert(sub_i_plus_1.filter(|x: i32| x > 0) == sub_i.filter(|x: i32| x > 0).push(input[i]));
    } else {
        assert(sub_i_plus_1.filter(|x: i32| x > 0) == sub_i.filter(|x: i32| x > 0));
    }
}

fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): simplified loop with lemma call */
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result@ == input@.subrange(0, i as int).filter(|x: i32| x > 0),
        decreases input.len() - i,
    {
        /* code modified by LLM (iteration 4): use lemma to prove invariant maintenance */
        proof {
            lemma_filter_subrange_extend(input@, i as int);
        }
        
        if input[i] > 0 {
            result.push(input[i]);
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): assert to prove postcondition from final loop invariant */
    assert(i == input.len());
    assert(input@.subrange(0, i as int) == input@);
    
    result
}

}
fn main() {}