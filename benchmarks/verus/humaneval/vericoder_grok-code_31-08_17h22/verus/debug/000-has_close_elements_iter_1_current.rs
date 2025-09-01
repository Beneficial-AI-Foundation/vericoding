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

    let sorted = numbers@.sort();

    let len = sorted.len();

    let mut i = 0;

    while i + 1 < len

        invariant

            forall|k: int, l: int| 0 <= k < l < i && sorted@[k] == sorted@[l] || abs(sorted@[k] - sorted@[l]) < threshold ==> exists|a: int, b: int| 0 <= a < b < numbers@.len() && abs(numbers@[a] - numbers@[b]) < threshold,

            i >= 0,

            i <= len,

            exists|k: int, l: int| 0 <= k < l < numbers@.len() && abs(numbers@[k] - numbers@[l]) < threshold ==> exists|a: int, b: int| 0 <= a < b < i && sorted@[a] == sorted@[b] || abs(sorted@[a] - sorted@[b]) < threshold,

    {

        if abs(sorted@[i] - sorted@[i+1]) < threshold {

            return true;

        }

        i += 1;

    }

    return false;

}
// </vc-code>

fn main() {}
}