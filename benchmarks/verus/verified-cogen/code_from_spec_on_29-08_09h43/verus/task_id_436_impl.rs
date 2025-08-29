use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_filter_push_negative<T>(s: Seq<T>, x: T, pred: spec_fn(T) -> bool)
    requires pred(x)
    ensures s.push(x).filter(pred) == s.filter(pred).push(x)
{
    /* code modified by LLM (iteration 5): added proof by induction on sequence length */
    if s.len() == 0 {
        assert(s.push(x) == seq![x]);
        assert(s.push(x).filter(pred) == seq![x]);
        assert(s.filter(pred) == seq![]);
        assert(s.filter(pred).push(x) == seq![x]);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_filter_push_negative(s_tail, x, pred);
        
        if pred(s[0]) {
            assert(s.push(x).filter(pred) == seq![s[0]] + s_tail.push(x).filter(pred));
            assert(s_tail.push(x).filter(pred) == s_tail.filter(pred).push(x));
            assert(s.push(x).filter(pred) == seq![s[0]] + s_tail.filter(pred).push(x));
            assert(s.filter(pred) == seq![s[0]] + s_tail.filter(pred));
            assert(s.filter(pred).push(x) == seq![s[0]] + s_tail.filter(pred).push(x));
        } else {
            assert(s.push(x).filter(pred) == s_tail.push(x).filter(pred));
            assert(s_tail.push(x).filter(pred) == s_tail.filter(pred).push(x));
            assert(s.filter(pred) == s_tail.filter(pred));
            assert(s.filter(pred).push(x) == s_tail.filter(pred).push(x));
        }
    }
}

proof fn lemma_filter_push_positive<T>(s: Seq<T>, x: T, pred: spec_fn(T) -> bool)
    requires !pred(x)
    ensures s.push(x).filter(pred) == s.filter(pred)
{
    /* code modified by LLM (iteration 5): added proof by induction on sequence length */
    if s.len() == 0 {
        assert(s.push(x) == seq![x]);
        assert(s.push(x).filter(pred) == seq![]);
        assert(s.filter(pred) == seq![]);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_filter_push_positive(s_tail, x, pred);
        
        if pred(s[0]) {
            assert(s.push(x).filter(pred) == seq![s[0]] + s_tail.push(x).filter(pred));
            assert(s_tail.push(x).filter(pred) == s_tail.filter(pred));
            assert(s.push(x).filter(pred) == seq![s[0]] + s_tail.filter(pred));
            assert(s.filter(pred) == seq![s[0]] + s_tail.filter(pred));
        } else {
            assert(s.push(x).filter(pred) == s_tail.push(x).filter(pred));
            assert(s_tail.push(x).filter(pred) == s_tail.filter(pred));
            assert(s.filter(pred) == s_tail.filter(pred));
        }
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    // post-conditions-start
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut negative_list: Vec<i32> = Vec::new();
    
    for i in 0..arr.len()
        invariant
            negative_list@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
    {
        /* code modified by LLM (iteration 5): fixed proof blocks with proper lemma application */
        if arr[i] < 0 {
            negative_list.push(arr[i]);
            proof {
                let old_subrange = arr@.subrange(0, i as int);
                let new_subrange = arr@.subrange(0, (i + 1) as int);
                assert(new_subrange == old_subrange.push(arr@[i as int]));
                assert(arr@[i as int] < 0);
                lemma_filter_push_negative(old_subrange, arr@[i as int], |x: i32| x < 0);
            }
        } else {
            proof {
                let old_subrange = arr@.subrange(0, i as int);
                let new_subrange = arr@.subrange(0, (i + 1) as int);
                assert(new_subrange == old_subrange.push(arr@[i as int]));
                assert(arr@[i as int] >= 0);
                lemma_filter_push_positive(old_subrange, arr@[i as int], |x: i32| x < 0);
            }
        }
    }
    
    /* code modified by LLM (iteration 5): fixed proof for postcondition */
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
    }
    
    negative_list
}
// </vc-code>

} // verus!

fn main() {}