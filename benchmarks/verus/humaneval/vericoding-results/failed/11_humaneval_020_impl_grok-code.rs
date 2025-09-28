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
{"    /* code modified by LLM (iteration 5): Fixed invariant syntax error by removing { } wrapper and inlining the map in forall; added invariants for inner loop to maintain correctness; ensured pair.0 <= pair.1 */
    proof {
        assert(numbers@.len() >= 2);
    }
    let n: usize = numbers.len();
    let mut best_pair: (i8, i8) = (numbers[0], numbers[1]);
    let mut best_diff: i32 = if (numbers[0] as i32) >= (numbers[1] as i32) {
        (numbers[0] as i32) - (numbers[1] as i32)
    } else {
        (numbers[1] as i32) - (numbers[0] as i32)
    };
    let mut outer_i: usize = 0;
    while outer_i < n
        invariant
            0 <= outer_i <= n,
            forall|k: int, l: int| 0 <= k < l < outer_i ==>
                abs_diff(numbers@.map(|_index, x| x as int)[k], numbers@.map(|_index, x| x as int)[l]) >= best_diff as int,
        decreases n - outer_i
    {
        let mut inner_j: usize = outer_i + 1;
        while inner_j < n
            invariant
                outer_i + 1 <= inner_j <= n,
                forall|k: int| 0 <= k < outer_i ==>
                    forall|l: int| outer_i <= l < inner_j ==>
                        abs_diff(numbers@.map(|_index, x| x as int)[k], numbers@.map(|_index, x| x as int)[l]) >= best_diff as int,
                forall|l: int| outer_i <= l < inner_j ==>
                    abs_diff(numbers@.map(|_index, x| x as int)[outer_i], numbers@.map(|_index, x| x as int)[l]) >= best_diff as int,
            decreases n - inner_j
        {
            let diff: i32 = if (numbers[outer_i] as i32) >= (numbers[inner_j] as i32) {
                (numbers[outer_i] as i32) - (numbers[inner_j] as i32)
            } else {
                (numbers[inner_j] as i32) - (numbers[outer_i] as i32)
            };
            if diff < best_diff {
                best_diff = diff;
                best_pair = if (numbers[outer_i] as i32) <= (numbers[inner_j] as i32) {
                    (numbers[outer_i], numbers[inner_j])
                } else {
                    (numbers[inner_j], numbers[outer_i])
                };
            }
            inner_j += 1;
        }
        outer_i += 1;
    }
    best_pair
}
// </vc-code>


}

fn main() {}