// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma with proper proof implementation */
spec fn is_even(x: u32) -> bool { x % 2 == 0 }

proof fn filter_subrange_lemma(arr: Seq<u32>, i: int, x: u32)
    requires 
        0 <= i < arr.len(),
        arr[i] == x,
    ensures arr.subrange(0, i + 1).filter(|y: u32| y % 2 == 0) == 
            if x % 2 == 0 { 
                arr.subrange(0, i).filter(|y: u32| y % 2 == 0).push(x) 
            } else { 
                arr.subrange(0, i).filter(|y: u32| y % 2 == 0) 
            }
{
    let sub_full = arr.subrange(0, i + 1);
    let sub_partial = arr.subrange(0, i);
    
    assert(sub_full == sub_partial.push(x));
    
    if x % 2 == 0 {
        assert(sub_full.filter(|y: u32| y % 2 == 0) == sub_partial.filter(|y: u32| y % 2 == 0).push(x));
    } else {
        assert(sub_full.filter(|y: u32| y % 2 == 0) == sub_partial.filter(|y: u32| y % 2 == 0));
    }
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by casting usize to int */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i
    {
        proof {
            assert(arr@[i as int] == arr[i as int]);
            filter_subrange_lemma(arr@, i as int, arr@[i as int]);
        }
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    result
}
// </vc-code>

}
fn main() {}