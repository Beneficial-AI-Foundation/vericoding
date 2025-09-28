// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix type conversions for abs_diff calls */
fn compute_abs_diff_int(a: i32, b: i32) -> i32 {
    if a >= b {
        a - b
    } else {
        b - a
    }
}

proof fn abs_diff_lemma(a: i32, b: i32)
    ensures compute_abs_diff_int(a, b) as int == self::abs_diff(a as int, b as int)
{
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
/* code modified by LLM (iteration 5): fix vector indexing in invariants by removing as usize cast */
{
    let n = numbers.len();
    for i in 0..n
        invariant
            forall|k: int| 0 <= k < (i as int) ==> 
                forall|l: int| k+1 <= l < (n as int) ==> 
                    self::abs_diff(numbers[k] as int, numbers[l] as int) >= threshold as int,
        decreases (n as int) - (i as int)
    {
        for j in (i+1)..n
            invariant
                forall|l: int| (i as int)+1 <= l < (j as int) ==> 
                    self::abs_diff(numbers[i] as int, numbers[l] as int) >= threshold as int,
            decreases (n as int) - (j as int)
        {
            let diff = compute_abs_diff_int(numbers[i], numbers[j]);
            if diff < threshold {
                proof {
                    abs_diff_lemma(numbers[i], numbers[j]);
                }
                return true;
            }
        }
    }
    return false;
}
// </vc-code>

}
fn main() {}