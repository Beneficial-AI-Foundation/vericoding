use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn filter_push_negative<T>(s: Seq<T>, x: T, pred: spec_fn(T) -> bool) -> bool {
    if pred(x) {
        s.filter(pred).push(x) == s.push(x).filter(pred)
    } else {
        s.filter(pred) == s.push(x).filter(pred)
    }
}

proof fn lemma_filter_push(s: Seq<i32>, x: i32)
    ensures filter_push_negative(s, x, |y: i32| y < 0)
{
    if x < 0 {
        assert(s.filter(|y: i32| y < 0).push(x) == s.push(x).filter(|y: i32| y < 0));
    } else {
        assert(s.filter(|y: i32| y < 0) == s.push(x).filter(|y: i32| y < 0));
    }
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    // post-conditions-start
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        proof {
            lemma_filter_push(arr@.subrange(0, i as int), arr@[i as int]);
        }
        
        if arr[i] < 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}