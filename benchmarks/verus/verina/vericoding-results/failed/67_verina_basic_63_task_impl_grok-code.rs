// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
fn exec_abs_diff(a: i32, b: i32) -> i32
    ensures exec_abs_diff(a, b) == abs_diff(a as int, b as int) as i32
{
    /* helper modified by LLM (iteration 3): added spec ensures for exec_abs_diff and implemented without abs */
    let diff: i64 = (a as i64) - (b as i64);
    if diff < 0 { (-diff) as i32 } else { diff as i32 }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &Vec<i32>, threshold: i32) -> (result: bool)
    requires threshold >= 0,
    ensures
        !result <==> (forall|i: int, j: int| 
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= threshold as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed syntax error in assert by wrapping casts in parentheses */
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            forall|k: int, m: int| 0 <= k < i && 0 <= m < numbers.len() && k != m ==> 
                abs_diff(numbers[k] as int, numbers[m] as int) >= threshold as int
    {
        let mut j: usize = i + 1;
        while j < numbers.len()
            invariant
                i < numbers.len(),
                forall|k: int, m: int| 0 <= k < i && 0 <= m < numbers.len() && k != m ==> 
                    abs_diff(numbers[k] as int, numbers[m] as int) >= threshold as int,
                forall|m: int| i + 1 <= m < j ==> 
                    abs_diff(numbers[i] as int, numbers[m] as int) >= threshold as int
        {
            let diff = exec_abs_diff(numbers[i], numbers[j]);
            if diff < threshold {
proof {
                assert!(abs_diff(numbers[i] as int, numbers[j] as int) == diff as int);
                assert!((diff as int) < (threshold as int));
}
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