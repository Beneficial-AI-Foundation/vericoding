use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 4): added helper lemma for filter property */
proof fn lemma_filter_push<T>(s: Seq<T>, x: T, pred: spec_fn(T) -> bool)
    ensures s.push(x).filter(pred) == s.filter(pred) + if pred(x) { seq![x] } else { seq![] }
{
    let s_pushed = s.push(x);
    let filtered_original = s.filter(pred);
    let filtered_pushed = s_pushed.filter(pred);
    
    assert forall |i: int| 0 <= i < s.len() implies s_pushed[i] == s[i] by {}
    assert(s_pushed[s.len()] == x);
    
    if pred(x) {
        assert(filtered_pushed == filtered_original + seq![x]);
    } else {
        assert(filtered_pushed == filtered_original);
        assert(seq![] == if pred(x) { seq![x] } else { seq![] });
    }
}

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    // post-conditions-start
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant and added proper verification */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0),
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 4): establish subrange relationship */
        assert(arr@.subrange(0, (i + 1) as int) == arr@.subrange(0, i as int).push(arr[i as int]));
        
        /* code modified by LLM (iteration 4): apply lemma to prove filter property */
        lemma_filter_push(arr@.subrange(0, i as int), arr[i as int], |x: u32| x % 2 != 0);
        
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 4): assert result maintains invariant */
            assert(result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0) + seq![arr[i as int]]);
            assert(result@ == arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0));
        } else {
            /* code modified by LLM (iteration 4): assert result maintains invariant for non-odd case */
            assert(result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 != 0));
            assert(result@ == arr@.subrange(0, (i + 1) as int).filter(|x: u32| x % 2 != 0));
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): establish postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, i as int) == arr@);
    
    result
}

} // verus!

fn main() {}