// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (replaced_list: Vec<i32>)

    requires
        first.len() > 0,

    ensures
        replaced_list@ == first@.subrange(0, first.len() - 1).add(second@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to fix loop verification */
    let mut result = Vec::new();
    let mut i = 0;
    while i < first.len() - 1
        invariant
            i <= first.len() - 1,
            result@ == first@.subrange(0, i as int),
        decreases first.len() - 1 - i,
    {
        result.push(first[i]);
        i += 1;
    }
    let mut j = 0;
    while j < second.len()
        invariant
            j <= second.len(),
            result@ == first@.subrange(0, first.len() - 1).add(second@.subrange(0, j as int)),
        decreases second.len() - j,
    {
        result.push(second[j]);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}