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
    /* code modified by LLM (iteration 5): fixed syntax error by adding missing comma in forall expression */
    let len = numbers.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|x: int, y: int| 0 <= x < y < i ==> abs_diff(seq_map_to_int(numbers@)[x], seq_map_to_int(numbers@)[y]) >= threshold as int,
    {
        let mut j = i + 1;
        while j < len
            invariant
                i + 1 <= j <= len,
                0 <= i < len,
                forall|x: int, y: int| 0 <= x < y < i ==> abs_diff(seq_map_to_int(numbers@)[x], seq_map_to_int(numbers@)[y]) >= threshold as int,
                forall|y: int| i as int < y < j as int ==> abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[y]) >= threshold as int,
        {
            let diff = if numbers[i] >= numbers[j] {
                numbers[i] - numbers[j]
            } else {
                numbers[j] - numbers[i]
            };
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


}

fn main() {}