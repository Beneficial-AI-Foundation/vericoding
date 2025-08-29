use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn min_fold(lengths: Seq<nat>) -> nat
{
    if lengths.len() == 0 {
        0
    } else {
        lengths.fold_left(lengths[0], |acc: nat, len: nat| if len < acc { len } else { acc })
    }
}

proof fn min_fold_subrange_lemma(lengths: Seq<nat>, i: int)
    requires 
        lengths.len() > 0,
        0 <= i < lengths.len() as int
    ensures
        min_fold(lengths.subrange(0, i + 1)) == 
        if lengths[i] < min_fold(lengths.subrange(0, i)) { 
            lengths[i] 
        } else { 
            min_fold(lengths.subrange(0, i)) 
        }
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)"
docstring: Implement smallest list length functionality.
*/
// </vc-description>

// <vc-spec>
fn smallest_list_length(lists: Vec<Vec<i32>>) -> (result: usize)
    requires lists.len() > 0
    ensures result == min_fold(lists@.map(|_i: int, list: Vec<i32>| list@.len() as nat)) as usize
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): converted length types to nat and cast result back to usize */
    let mut min_length = lists[0].len();
    let mut i = 1;
    
    while i < lists.len()
        invariant 
            0 < lists.len(),
            i <= lists.len(),
            min_length == min_fold(lists@.subrange(0, i as int).map(|_j: int, list: Vec<i32>| list@.len() as nat)) as usize
    {
        if lists[i].len() < min_length {
            min_length = lists[i].len();
        }
        i += 1;
    }
    
    min_length
}
// </vc-code>

fn main() {}
}