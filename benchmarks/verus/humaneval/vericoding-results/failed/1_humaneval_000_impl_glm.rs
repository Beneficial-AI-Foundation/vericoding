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
fn abs_diff_impl(a: int, b: int) -> (result: int)
    ensures result == if a >= b { a - b } else { b - a }
{
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
{
    let numbers_int = seq_map_to_int(numbers@);
    let n = numbers_int.len();
    let mut i = 0;
    let mut result = false;
    
    while i < n
        invariant 0 <= i <= n,
        invariant result == exists|j: int, k: int| 
            0 <= j < k < i && abs_diff(numbers_int[j], numbers_int[k]) < threshold as int
        decreases n - i
    {
        let mut j = 0;
        while j < i
            invariant 0 <= j <= i,
            invariant result == exists|k: int, l: int| 
                0 <= k < l < i && abs_diff(numbers_int[k], numbers_int[l]) < threshold as int
            decreases i - j
        {
            let diff = abs_diff_impl(numbers_int[i], numbers_int[j]);
            if diff < threshold as int {
                result = true;
                break;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}