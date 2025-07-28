use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 3): added helper lemma to prove subrange extension property */
proof fn lemma_subrange_extension<T>(s: Seq<T>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
}

/* code modified by LLM (iteration 3): provided proof body for filter_push lemma */
proof fn lemma_filter_push<T>(s: Seq<T>, elem: T, pred: spec_fn(T) -> bool)
    ensures (s.push(elem)).filter(pred) == 
            if pred(elem) { s.filter(pred).push(elem) } else { s.filter(pred) }
{
    let extended = s.push(elem);
    let filtered_extended = extended.filter(pred);
    let filtered_s = s.filter(pred);
    
    if pred(elem) {
        // When pred(elem) is true, elem should be included in the filtered result
        assert(filtered_extended == filtered_s.push(elem));
    } else {
        // When pred(elem) is false, elem should not be included in the filtered result
        assert(filtered_extended == filtered_s);
    }
}

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    // post-conditions-start
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): simplified loop invariant */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 3): use helper lemmas to prove invariant maintenance */
        proof {
            lemma_subrange_extension(arr@, i as int);
            lemma_filter_push(arr@.subrange(0, i as int), arr[i as int], |x: i32| x < 0);
        }
        
        if arr[i] < 0 {
            result.push(arr[i]);
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): simplified final proof */
    proof {
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    result
}

} // verus!

fn main() {}