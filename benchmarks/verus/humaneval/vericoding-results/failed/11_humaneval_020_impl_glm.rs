// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(x: int, y: int) -> int {
        if x >= y { x - y } else { y - x }
    }
    
spec fn valid_input(numbers: Seq<int>) -> bool {
        numbers.len() >= 2
    }
    
spec fn is_optimal_pair(numbers: Seq<int>, pair: (int, int)) -> bool {
        numbers.contains(pair.0) &&
        numbers.contains(pair.1) &&
        pair.0 <= pair.1 &&
        forall|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==>
            abs_diff(numbers[i], numbers[j]) >= abs_diff(pair.0, pair.1)
    }
    
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added executable abs_diff_i8 function */
exec fn abs_diff_i8(a: i8, b: i8) -> u8 {
    let a32 = a as i32;
    let b32 = b as i32;
    if a32 >= b32 {
        (a32 - b32) as u8
    } else {
        (b32 - a32) as u8
    }
}
// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(numbers@.map(|_index, x| x as int))
    ensures is_optimal_pair(numbers@.map(|_index, x| x as int), (result.0 as int, result.1 as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed tuple comparison by breaking into component comparisons */
{
    let a0 = numbers[0];
    let a1 = numbers[1];
    let x0 = if a0 <= a1 { a0 } else { a1 };
    let y0 = if a0 <= a1 { a1 } else { a0 };
    let mut min_diff = abs_diff_i8(a0, a1);
    let mut result = (x0, y0);
    let n = numbers.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            min_diff == abs_diff_i8(result.0, result.1),
    {
        let mut j = i + 1;
        while j < n
            invariant
                i < j <= n,
        {
            let a = numbers[i];
            let b = numbers[j];
            let diff = abs_diff_i8(a, b);
            let x = if a <= b { a } else { b };
            let y = if a <= b { b } else { a };
            if diff < min_diff || (diff == min_diff && (x < result.0 || (x == result.0 && y < result.1))) {
                result = (x, y);
                min_diff = diff;
            }
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}