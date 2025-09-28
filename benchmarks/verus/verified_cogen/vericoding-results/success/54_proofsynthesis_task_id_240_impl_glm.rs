// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed problematic assert statement */
proof fn replace_last_element_lemma(first: &Vec<i32>, second: &Vec<i32>)
    requires
        first.len() > 0,
    ensures
        first@.subrange(0, first.len() - 1).add(second@) ==
            first@.subrange(0, first.len() - 1) + second@
{
    // This is true by definition of the `add` method for sequences.
}
// </vc-helpers>

// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)

    requires
        first.len() > 0,

    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes needed as implementation was correct */
{
    let mut replaced_list = Vec::new();
    
    for i in 0..first.len() - 1
        invariant
            0 <= i <= first.len() - 1,
            replaced_list@ == first@.subrange(0, i as int),
    {
        replaced_list.push(first[i]);
    }
    
    for j in 0..second.len()
        invariant
            0 <= j <= second.len(),
            replaced_list@ == first@.subrange(0, (first.len() - 1) as int).add(second@.subrange(0, j as int)),
    {
        replaced_list.push(second[j]);
    }
    
    replaced_list
}
// </vc-code>

}
fn main() {}