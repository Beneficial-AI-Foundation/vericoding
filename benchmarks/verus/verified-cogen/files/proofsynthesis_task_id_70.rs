// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn all_sequence_equal_length(seq: &Vec<Vec<i32>>) -> (result: bool)

    requires
        seq.len() > 0,

    ensures
        result == (forall|i: int, j: int|
            (0 <= i < seq.len() && 0 <= j < seq.len()) ==> (#[trigger] seq[i].len()
                == #[trigger] seq[j].len())),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}