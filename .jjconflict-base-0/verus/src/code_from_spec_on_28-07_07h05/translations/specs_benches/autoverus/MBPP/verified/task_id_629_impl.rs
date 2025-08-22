use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

/* code modified by LLM (iteration 3): added helper lemma for filter property */
proof fn lemma_filter_push_even(s: Seq<u32>, x: u32)
    requires x % 2 == 0
    ensures s.filter(|y: u32| y % 2 == 0).push(x) == s.push(x).filter(|y: u32| y % 2 == 0)
{
    let filtered_s = s.filter(|y: u32| y % 2 == 0);
    let s_push_x = s.push(x);
    let filtered_s_push_x = filtered_s.push(x);
    let s_push_x_filtered = s_push_x.filter(|y: u32| y % 2 == 0);
    
    assert forall |i: int| 0 <= i < filtered_s_push_x.len() implies 
        filtered_s_push_x[i] == s_push_x_filtered[i] by {
        if i < filtered_s.len() {
            assert(filtered_s_push_x[i] == filtered_s[i]);
        } else {
            assert(i == filtered_s.len());
            assert(filtered_s_push_x[i] == x);
        }
    };
}

/* code modified by LLM (iteration 3): added helper lemma for filter property when element is odd */
proof fn lemma_filter_push_odd(s: Seq<u32>, x: u32)
    requires x % 2 != 0
    ensures s.filter(|y: u32| y % 2 == 0) == s.push(x).filter(|y: u32| y % 2 == 0)
{
    let filtered_s = s.filter(|y: u32| y % 2 == 0);
    let s_push_x = s.push(x);
    let s_push_x_filtered = s_push_x.filter(|y: u32| y % 2 == 0);
    
    assert forall |i: int| 0 <= i < filtered_s.len() implies 
        filtered_s[i] == s_push_x_filtered[i] by {
        // The filtered sequences are the same since x is odd and gets filtered out
    };
}

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): simplified loop invariant and proof structure */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 3): use helper lemma to prove filter property */
            lemma_filter_push_even(arr@.subrange(0, i as int), arr[i as int]);
            assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr[i as int]));
        } else {
            /* code modified by LLM (iteration 3): use helper lemma to prove filter property */
            lemma_filter_push_odd(arr@.subrange(0, i as int), arr[i as int]);
            assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr[i as int]));
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): establish postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!