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
    /* code modified by LLM (iteration 4): Fixed type error by using 'as int' conversion */
    let first_len = seq[0].len();
    let mut i = 1;
    while i < seq.len()
        invariant
            1 <= i <= seq.len(),
            forall|j: int| 0 <= j < i ==> seq[j].len() == first_len,
        decreases seq.len() - i,
    {
        if seq[i].len() != first_len {
            assert(seq[i as int].len() != seq[0].len());
            return false;
        }
        i += 1;
    }
    assert(forall|j: int| 0 <= j < seq.len() ==> seq[j].len() == first_len);
    assert(forall|i: int, j: int| 0 <= i < seq.len() && 0 <= j < seq.len() ==> seq[i].len() == seq[j].len());
    true
}
// </vc-code>

}
fn main() {}