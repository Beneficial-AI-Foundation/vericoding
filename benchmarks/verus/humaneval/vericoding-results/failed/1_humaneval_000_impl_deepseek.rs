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
/* helper modified by LLM (iteration 5): fixed type conversion to avoid compilation errors */
fn find_close_pair(numbers: &Vec<i8>, threshold: i8, i: usize, j: usize) -> (result: bool)
    requires
        i < numbers.len(),
        j > i,
        j < numbers.len(),
        threshold >= 0,
    ensures
        result == (abs_diff(numbers[i] as int, numbers[j] as int) < threshold as int)
{
    let a = numbers[i] as int;
    let b = numbers[j] as int;
    let diff = if a >= b { a - b } else { b - a };
    diff < threshold as int
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Vec<i8>, threshold: i8) -> (result: bool)
    requires valid_input(seq_map_to_int(numbers@), threshold as int)
    ensures result == has_close_elements(seq_map_to_int(numbers@), threshold as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversions in assertions to avoid compilation errors */
    let n = numbers.len();
    let mut i: usize = 0;

    while i < n
        invariant
            i <= n,
            forall|k: int, l: int| 0 <= k < l < i as int ==> abs_diff(numbers[k] as int, numbers[l] as int) >= threshold as int
        decreases n - i
    {
        let mut j = i + 1;
        
        while j < n
            invariant
                j <= n,
                i < j,
                forall|k: int| j as int <= k < n as int ==> abs_diff(numbers[i] as int, numbers[k] as int) >= threshold as int
            decreases n - j
        {
            let close = find_close_pair(&numbers, threshold, i, j);
            if close {
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