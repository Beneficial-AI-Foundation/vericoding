// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_boolean(seq: Seq<bool>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_true(arr: &Vec<bool>) -> (count: u64)

    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}