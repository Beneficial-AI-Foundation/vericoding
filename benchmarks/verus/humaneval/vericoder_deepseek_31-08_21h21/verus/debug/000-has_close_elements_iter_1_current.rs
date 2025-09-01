use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: i64, b: i64) -> i64 {
    if a > b { a - b } else { b - a }
}

proof fn abs_diff_commutative(a: i64, b: i64)
    ensures
        abs_diff(a, b) == abs_diff(b, a)
{
}

proof fn abs_diff_nonnegative(a: i64, b: i64)
    ensures
        abs_diff(a, b) >= 0
{
}

proof fn distance_symmetric(numbers: Seq<i64>, i: int, j: int)
    requires
        0 <= i < numbers.len(),
        0 <= j < numbers.len(),
    ensures
        abs_diff(numbers[i], numbers[j]) == abs_diff(numbers[j], numbers[i]),
{
    abs_diff_commutative(numbers[i], numbers[j]);
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
    let n = numbers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < i, 0 <= l < n ==> 
                !(k < l && abs_diff(numbers[k], numbers[l]) < threshold),
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < j <= n,
                forall|l: int| i < l < j ==> !(abs_diff(numbers[i], numbers[l]) < threshold),
        {
            let diff = abs_diff(numbers[i], numbers[j]);
            if diff < threshold {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {}
}