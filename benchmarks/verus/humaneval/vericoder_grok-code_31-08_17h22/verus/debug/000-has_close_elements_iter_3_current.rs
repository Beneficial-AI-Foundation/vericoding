use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
use vstd::math::*;
use vstd::prelude::*;

verus! {
    spec fn i64_abs_spec(a: i64) -> i64 {
        if a < 0 {
            -a
        } else {
            a
        }
    }

    fn i64_abs(a: i64) -> i64 {
        if a < 0 {
            -a
        } else {
            a
        }
    }
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
    let mut temp = Vec::<i64>::with_capacity(numbers.len());
    temp.extend_from_slice(numbers);
    temp.sort();
    proof {
        // Sorting preserves the length
        assert(temp@.len() == numbers@.len());
    }
    ghost let sorted = temp@;
    let temp_len: int = temp@.len();

    let mut i = 0;

    while i + 1 < temp_len
        invariant
            forall|k: int, l: int| 0 <= k < l < i ==> i64_abs_spec(sorted@[k] - sorted@[l]) < threshold ==> exists|a: int, b: int| 0 <= a < b < numbers@.len() && abs(numbers@[a] - numbers@[b]) < threshold,
            i >= 0,
            i <= temp_len,
            exists|k: int, l: int| 0 <= k < l < numbers@.len() && abs(numbers@[k] - numbers@[l]) < threshold ==> exists|a: int, b: int| 0 <= a < b < i && i64_abs_spec(sorted@[a] - sorted@[b]) < threshold,
    {
        if i64_abs(sorted@[i] - sorted@[i+1]) < threshold {
            proof {
                let a = sorted@[i];
                let b = sorted@[i+1];
                assert(i64_abs(a - b) < threshold);
                // Assert existence of indices k, l in numbers where numbers@[k] == a, numbers@[l] == b with k < l
                assert(exists|k: int, l: int| 0 <= k < l < numbers@.len() && numbers@[k] == a && numbers@[l] == b);
                // Assert the absolute difference condition using spec abs
                assert(abs(a as int - b as int) == abs(a - b));
                assert(exists|k: int, l: int| 0 <= k < l < numbers@.len() && abs(numbers@[k] - numbers@[l]) < threshold);
            }
            return true;
        }
        i += 1;
    }
    return false;
}
// </vc-code>

fn main() {}
}