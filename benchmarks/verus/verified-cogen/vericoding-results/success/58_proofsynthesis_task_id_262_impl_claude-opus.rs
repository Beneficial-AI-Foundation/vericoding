// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_array(list: &Vec<i32>, l: usize) -> (new_list: (Vec<i32>, Vec<i32>))

    requires
        list@.len() > 0,
        0 < l < list@.len(),

    ensures
        new_list.0@ == list@.subrange(0, l as int),
        new_list.1@ == list@.subrange(l as int, list.len() as int),
// </vc-spec>
// <vc-code>
{
    let mut first = Vec::new();
    let mut second = Vec::new();
    
    let mut i: usize = 0;
    while i < l
        invariant
            i <= l,
            l < list.len(),
            first@ == list@.subrange(0, i as int),
        decreases l - i,
    {
        first.push(list[i]);
        i = i + 1;
    }
    
    let mut j: usize = l;
    while j < list.len()
        invariant
            l <= j <= list.len(),
            first@ == list@.subrange(0, l as int),
            second@ == list@.subrange(l as int, j as int),
        decreases list.len() - j,
    {
        second.push(list[j]);
        j = j + 1;
    }
    
    (first, second)
}
// </vc-code>

}
fn main() {}