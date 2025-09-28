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

// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(numbers@.map(|_index, x| x as int))
    ensures is_optimal_pair(numbers@.map(|_index, x| x as int), (result.0 as int, result.1 as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type errors by using ghost variables for int operations */
    let n = numbers.len();
    
    // Initialize with first two elements in sorted order
    let mut result: (i8, i8) = if numbers[0] <= numbers[1] {
        (numbers[0], numbers[1])
    } else {
        (numbers[1], numbers[0])
    };
    
    let mut min_diff: i8 = if result.1 >= result.0 {
        result.1 - result.0
    } else {
        result.0 - result.1
    };
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == numbers.len(),
            n >= 2,
            min_diff >= 0,
            min_diff <= 127,
            result.0 <= result.1,
            abs_diff(result.0 as int, result.1 as int) == min_diff as int,
            exists|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b &&
                numbers[a] == result.0 && numbers[b] == result.1,
            forall|a: int, b: int| 0 <= a <= i && 0 <= b < n && a < b ==>  
                abs_diff(numbers[a] as int, numbers[b] as int) >= min_diff as int,
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < n,
                i + 1 <= j,
                j <= n,
                n == numbers.len(),
                n >= 2,
                min_diff >= 0,
                min_diff <= 127,
                result.0 <= result.1,
                abs_diff(result.0 as int, result.1 as int) == min_diff as int,
                exists|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b &&
                    numbers[a] == result.0 && numbers[b] == result.1,
                forall|a: int, b: int| (0 <= a <= i && 0 <= b < n && a < b && b < j) || (0 <= a < i && 0 <= b < n && a < b) ==>  
                    abs_diff(numbers[a] as int, numbers[b] as int) >= min_diff as int,
            decreases n - j
        {
            // Compute difference using i8 arithmetic
            let diff_i8: i8 = if numbers[j] >= numbers[i] {
                numbers[j] - numbers[i]
            } else {
                numbers[i] - numbers[j]
            };
            
            proof {
                let ghost diff_int = abs_diff(numbers[i] as int, numbers[j] as int);
                assert(diff_i8 as int == diff_int);
            }
            
            if diff_i8 < min_diff {
                min_diff = diff_i8;
                if numbers[i] <= numbers[j] {
                    result = (numbers[i], numbers[j]);
                } else {
                    result = (numbers[j], numbers[i]);
                }
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