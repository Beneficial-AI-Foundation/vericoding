use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
/* No helpers needed */
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
    // impl-start
    let n_usize: usize = numbers.len();
    let n_int: int = numbers@.len() as int;

    let mut i: usize = 0;
    while i < n_usize
        invariant 0 <= (i as int) && (i as int) <= n_int;
        invariant forall|a: int, b: int| 0 <= a && a < b && b < (i as int) ==> !(abs(numbers@[a as usize] - numbers@[b as usize]) < threshold);
        decreases n_usize - i
    {
        let mut j: usize = i + 1;
        while j < n_usize
            invariant 0 <= (i as int) && (i as int) < n_int;
            invariant 0 <= (j as int) && (j as int) <= n_int;
            invariant forall|a: int, b: int| 0 <= a && a < b && b < (i as int) ==> !(abs(numbers@[a as usize] - numbers@[b as usize]) < threshold);
            invariant forall|b: int| (i as int) < b && b < (j as int) ==> !(abs(numbers@[i as usize] - numbers@[b as usize]) < threshold);
            decreases n_usize - j
        {
            if abs(numbers[i] - numbers[j]) < threshold {
                let ii: int = i as int;
                let jj: int = j as int;
                proof {
                    assert(0 <= ii && ii < jj && jj < n_int);
                    assert(abs(numbers[i] - numbers[j]) < threshold);
                    assert(exists|a: int, b: int|
                        0 <= a && a < b && b < n_int && abs(numbers@[a as usize] - numbers@[b as usize]) < threshold
                    ) by {
                        witness ii, jj;
                    }
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    proof {
        // From the outer loop invariant with i == n_int, we get that no such pair exists.
        assert(i == n_usize);
        assert((i as int) == n_int);
        assert(forall|a: int, b: int| 0 <= a && a < b && b < n_int ==> !(abs(numbers@[a as usize] - numbers@[b as usize]) < threshold)));
        assert(!exists|a: int, b: int| 0 <= a && a < b && b < n_int && abs(numbers@[a as usize] - numbers@[b as usize]) < threshold);
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}