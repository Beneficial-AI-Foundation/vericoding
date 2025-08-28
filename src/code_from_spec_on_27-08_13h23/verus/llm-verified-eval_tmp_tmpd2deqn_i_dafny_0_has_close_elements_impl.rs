use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    abs(a - b)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
{
    if numbers.len() <= 1 {
        return false;
    }

    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            forall|k: int, l: int|
                0 <= k < i &&
                0 <= l < numbers.len() &&
                k != l ==>
                abs_diff(numbers[k], numbers[l]) >= threshold,
    {
        let mut j: usize = 0;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                0 <= j <= numbers.len(),
                forall|k: int, l: int|
                    0 <= k < i &&
                    0 <= l < numbers.len() &&
                    k != l ==>
                    abs_diff(numbers[k], numbers[l]) >= threshold,
                forall|l: int|
                    0 <= l < j &&
                    i != l as usize ==>
                    abs_diff(numbers[i as int], numbers[l]) >= threshold,
        {
            if i != j && abs_diff(numbers[i as int], numbers[j as int]) < threshold {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}

}