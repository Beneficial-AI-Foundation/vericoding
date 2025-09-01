use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let numbers_seq = numbers@;
    let len = numbers_seq.len();
    for i in 0..len {
        for j in (i + 1)..len {
            if abs(numbers_seq[i] - numbers_seq[j]) < threshold {
                proof {
                    assert (exists |i_: int, j_: int| 0 <= i_ < j_ < numbers_seq.len() && #[trigger] abs(numbers_seq[i_] - numbers_seq[j_]) < threshold) by {
                        exists i@, j@;
                    }
                }
                return true;
            }
        }
    }
    proof {
        assert (forall |i_, j_: int| 0 <= i_ < j_ < numbers_seq.len() ==> !(#[trigger] abs(numbers_seq[i_] - numbers_seq[j_]) < threshold));
    }
    return false;
}
// </vc-code>

fn main() {}
}