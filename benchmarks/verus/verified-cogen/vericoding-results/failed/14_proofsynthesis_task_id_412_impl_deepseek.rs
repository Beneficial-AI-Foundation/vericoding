// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax with proper braces */
proof fn filter_preserves_elements(seq: Seq<u32>, pred: spec_fn(u32) -> bool) -> (res: Seq<u32>)
    decreases seq.len()
    ensures
        res == seq.filter(pred)
{
    if seq.len() == 0 {
        Seq::empty()
    } else {
        let first = seq[0];
        let rest = seq.subrange(1, seq.len() as int);
        let rest_filtered = filter_preserves_elements(rest, pred);
        if pred(first) {
            rest_filtered.insert(0, first)
        } else {
            rest_filtered
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed ensures clause syntax */
{
    let mut even_list: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            even_list@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
            i <= arr.len(),
    {
        if arr[i] % 2 == 0 {
            even_list.push(arr[i]);
        }
        i = i + 1;
    }
    
    proof {
        let full_filtered = filter_preserves_elements(arr@, |x: u32| x % 2 == 0);
        assert(even_list@ == full_filtered);
    }
    
    even_list
}
// </vc-code>

}
fn main() {}