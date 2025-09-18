// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed overflow by using int arithmetic and sequence access */
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            forall|ii: int, jj: int| 
                0 <= ii < i && 0 <= jj < numbers.len() && ii != jj ==> 
                abs_diff(numbers@[ii] as int, numbers@[jj] as int) >= threshold as int,
            forall|ii: int, jj: int| 
                0 <= ii < numbers.len() && 0 <= jj < i && ii != jj ==> 
                abs_diff(numbers@[ii] as int, numbers@[jj] as int) >= threshold as int,
        decreases numbers.len() - i
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                0 <= j <= numbers.len(),
                forall|jj: int| #![auto]
                    0 <= jj < j && i != jj ==> 
                    abs_diff(numbers@[i as int] as int, numbers@[jj] as int) >= threshold as int,
            decreases numbers.len() - j
        {
            if i != j {
                let val_i = numbers@[i as int] as int;
                let val_j = numbers@[j as int] as int;
                let diff = abs_diff(val_i, val_j);
                if diff < threshold as int {
                    return true;
                }
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