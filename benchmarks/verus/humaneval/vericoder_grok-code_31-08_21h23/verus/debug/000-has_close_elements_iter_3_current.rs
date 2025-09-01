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
    let len = numbers_seq.len() as usize;
    for i in 0..len {
        let i_nat = i as nat;
        for j in (i + 1)..len {
            let j_nat = j as nat;
            if abs((numbers_seq[i_nat] as int) - (numbers_seq[j_nat] as int)) < (threshold as int) {
                proof {
                    let i_int = i as int;
                    let j_int = j as int;
                    assert(0 <= i_int < j_int < numbers_seq.len());
                    assert(abs((numbers_seq[i_nat] as int) - (numbers_seq[j_nat] as int)) < (threshold as int));
                }
                return true;
            }
        }
    }
    proof {
        assert (forall |i_: int, j_: int| 0 <= i_ < j_ < numbers_seq.len() ==> !(abs((numbers_seq[(i_ as usize) as nat] as int) - (numbers_seq[(j_ as usize) as nat] as int)) < (threshold as int)));
    }
    return false;
}
// </vc-code>

fn main() {}
}