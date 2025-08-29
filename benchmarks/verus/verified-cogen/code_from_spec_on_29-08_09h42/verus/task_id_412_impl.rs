use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove filter properties across subrange extensions
proof fn lemma_filter_extend(arr: Seq<u32>, i: int, x: u32)
    requires 
        0 <= i < arr.len(),
        arr[i] == x,
    ensures
        arr.subrange(0, i + 1).filter(|y: u32| y % 2 == 0) == 
        if x % 2 == 0 {
            arr.subrange(0, i).filter(|y: u32| y % 2 == 0).push(x)
        } else {
            arr.subrange(0, i).filter(|y: u32| y % 2 == 0)
        }
{
    let sub_i = arr.subrange(0, i);
    let sub_i1 = arr.subrange(0, i + 1);
    assert(sub_i1 == sub_i.push(x));
}
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    // post-conditions-start
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): fixed type casting for arr[i] access */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| x % 2 == 0),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            result.push(arr[i]);
            /* code modified by LLM (iteration 5): fixed indexing with int cast */
            proof {
                lemma_filter_extend(arr@, i as int, arr@[i as int]);
            }
        } else {
            /* code modified by LLM (iteration 5): fixed indexing with int cast */
            proof {
                lemma_filter_extend(arr@, i as int, arr@[i as int]);
            }
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 5): final proof that subrange equals full array */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}