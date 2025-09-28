// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_and_append(list: &Vec<i32>, n: usize) -> (new_list: Vec<i32>)

    requires
        list@.len() > 0,
        0 < n < list@.len(),

    ensures
        new_list@ == list@.subrange(n as int, list@.len() as int).add(list@.subrange(0, n as int)),
// </vc-spec>
// <vc-code>
{
    let mut left = list.clone();
    let mut right = left.split_off(n);
    right.append(&mut left);
    right
}
// </vc-code>

}
fn main() {}