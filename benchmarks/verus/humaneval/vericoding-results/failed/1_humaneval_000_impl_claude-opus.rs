// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(numbers: Seq<int>, threshold: int) -> bool {
    true
}

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

spec fn has_close_elements(numbers: Seq<int>, threshold: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < numbers.len() && abs_diff(numbers[i], numbers[j]) < threshold
}

spec fn seq_map_to_int(numbers: Seq<i8>) -> Seq<int> {
        numbers.map(|_i: int, x: i8| x as int)
}
    

// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Vec<i8>, threshold: i8) -> (result: bool)
    requires valid_input(seq_map_to_int(numbers@), threshold as int)
    ensures result == has_close_elements(seq_map_to_int(numbers@), threshold as int)
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    for i in 0..n
        invariant
            forall|a: int, b: int| 0 <= a < i && a < b < n ==> abs_diff(seq_map_to_int(numbers@)[a], seq_map_to_int(numbers@)[b]) >= threshold as int
    {
        for j in (i + 1)..n
            invariant
                forall|b: int| i < b < j ==> abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[b]) >= threshold as int,
                forall|a: int, b: int| 0 <= a < i && a < b < n ==> abs_diff(seq_map_to_int(numbers@)[a], seq_map_to_int(numbers@)[b]) >= threshold as int
        {
            let diff = if numbers[i] >= numbers[j] {
                numbers[i] - numbers[j]
            } else {
                numbers[j] - numbers[i]
            };
            if diff < threshold {
                assert(abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int]) < threshold as int);
                return true;
            }
        }
    }
    assert(forall|a: int, b: int| 0 <= a < b < n ==> abs_diff(seq_map_to_int(numbers@)[a], seq_map_to_int(numbers@)[b]) >= threshold as int);
    false
}
// </vc-code>


}

fn main() {}