// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn rotation_split(len: usize, n: usize) -> (result: int) {
    len - (n % len)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rotate_right(list: &Vec<u32>, n: usize) -> (new_list: Vec<u32>)

    requires
        list.len() > 0,

    ensures
        new_list.len() == list.len(),
        new_list@ == list@.subrange(rotation_split(list.len(), n) as int, list@.len() as int).add(
            list@.subrange(0, rotation_split(list.len(), n) as int),
        ),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}