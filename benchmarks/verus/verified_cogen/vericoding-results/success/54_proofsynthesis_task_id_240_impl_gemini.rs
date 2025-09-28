// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added invariant to carry precondition into loop */
fn copy_prefix(v: &Vec<i32>, len: usize) -> (prefix: Vec<i32>)
    requires
        len <= v.len(),
    ensures
        prefix@ == v@.subrange(0, len as int),
{
    let mut prefix_vec = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            len <= v.len(),
            prefix_vec@ == v@.subrange(0, i as int),
        decreases len - i,
    {
        prefix_vec.push(v[i]);
        i = i + 1;
    }
    prefix_vec
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
{
    /* code modified by LLM (iteration 3): no changes, as errors were in the helper function */
    let len_minus_one = first.len() - 1;
    let mut replaced_list = copy_prefix(first, len_minus_one);

    let mut j: usize = 0;
    while j < second.len()
        invariant
            j <= second.len(),
            replaced_list@ == first@.subrange(0, len_minus_one as int).add(second@.subrange(0, j as int)),
        decreases second.len() - j,
    {
        replaced_list.push(second[j]);
        j = j + 1;
    }

    replaced_list
}
// </vc-code>

}
fn main() {}