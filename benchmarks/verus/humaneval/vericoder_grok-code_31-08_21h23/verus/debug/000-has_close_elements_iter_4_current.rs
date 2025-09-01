use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: i64, b: i64) -> int {
    abs(a as int - b as int)
}

#[verifier::spec]
fn abs_less(a: i64, b: i64, threshold: i64) -> bool {
    abs_diff(a, b) < threshold as int
}
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
    let len_u = numbers_seq.len() as usize;
    for i: usize in 0..len_u {
        proof {
            let i_int = i as int;
        }
        for j: usize in (i + 1)..len_u {
            proof {
                let j_int = j as int;
            }
            let diff = (numbers[i] as i128 - numbers[j] as i128).abs() as i128;
            proof {
                assert(abs_diff(numbers[i], numbers[j]) == diff as int);
            }
            if diff < threshold as i128 {
                proof {
                    if threshold as i128 > 0 {
                        assert(abs(numbers_seq[i_int] - numbers_seq[j_int]) == diff as int);
                        assert(abs(numbers_seq[i_int] - numbers_seq[j_int]) < threshold as int);
                    }
                }
                return true;
            } else {
                proof {
                    assert(abs_diff(numbers[i], numbers[j]) >= threshold as int);
                }
            }
        }
    }
    return false;
}
// </vc-code>

fn main() {}
}