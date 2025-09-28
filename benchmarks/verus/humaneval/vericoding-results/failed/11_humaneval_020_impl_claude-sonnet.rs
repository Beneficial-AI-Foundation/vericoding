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
/* helper modified by LLM (iteration 5): helper to compute absolute difference of i8 values with overflow protection */
fn abs_diff_i8(x: i8, y: i8) -> (result: i8)
    requires
        !(x == i8::MIN && y > 0),
        !(y == i8::MIN && x > 0),
    ensures
        result >= 0,
        result as int == abs_diff(x as int, y as int),
{
    if x >= y {
        x - y
    } else {
        y - x
    }
}
// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(numbers@.map(|_index, x| x as int))
    ensures is_optimal_pair(numbers@.map(|_index, x| x as int), (result.0 as int, result.1 as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): initialize with safe values and ensure optimal pair conditions */
    let mut min_diff: i8 = 127; // i8::MAX
    let mut result_pair = (numbers[0], numbers[1]);
    
    // Find the actual minimum difference first
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            numbers.len() >= 2,
            min_diff >= 0,
            numbers@.map(|_index, x| x as int).contains(result_pair.0 as int),
            numbers@.map(|_index, x| x as int).contains(result_pair.1 as int),
            result_pair.0 <= result_pair.1,
        decreases numbers.len() - i
    {
        let mut j = i + 1;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                i + 1 <= j <= numbers.len(),
                min_diff >= 0,
                numbers@.map(|_index, x| x as int).contains(result_pair.0 as int),
                numbers@.map(|_index, x| x as int).contains(result_pair.1 as int),
                result_pair.0 <= result_pair.1,
            decreases numbers.len() - j
        {
            if !(numbers[i] == i8::MIN && numbers[j] > 0) {
                if !(numbers[j] == i8::MIN && numbers[i] > 0) {
                    let current_diff = abs_diff_i8(numbers[i], numbers[j]);
                    if current_diff < min_diff {
                        min_diff = current_diff;
                        result_pair = if numbers[i] <= numbers[j] { (numbers[i], numbers[j]) } else { (numbers[j], numbers[i]) };
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    result_pair
}
// </vc-code>


}

fn main() {}