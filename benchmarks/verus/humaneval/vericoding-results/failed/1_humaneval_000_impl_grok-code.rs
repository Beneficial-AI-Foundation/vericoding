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
/* helper modified by LLM (iteration 5): add exec helper for abs_diff */
fn abs_diff_exec(a: i8, b: i8) -> i8 {
    if a >= b {
        a - b
    } else {
        b - a
    }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Vec<i8>, threshold: i8) -> (result: bool)
    requires valid_input(seq_map_to_int(numbers@), threshold as int)
    ensures result == has_close_elements(seq_map_to_int(numbers@), threshold as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): remove erroneous forall to fix compilation */
{
    let seq_int: Ghost<Seq<int>> = seq_map_to_int(numbers@);
    let mut found: bool = false;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            !has_close_elements(seq_int@.take(i as int), threshold as int),
    {
        let mut j: usize = i + 1;
        while j < numbers.len()
            invariant
                i < j <= numbers.len(),
        {
            if abs_diff_exec(numbers[i], numbers[j]) < threshold {
                found = true;
                break;
            }
            j = j + 1;
        }
        if found {
            break;
        }
        i = i + 1;
    }
    found
}
// </vc-code>


}

fn main() {}