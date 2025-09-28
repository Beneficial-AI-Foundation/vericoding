// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed index type issues by using proper int casting */
proof fn lemma_close_elements_found(numbers: &Vec<i32>, threshold: i32, i: usize, j: usize)
    requires
        threshold >= 0,
        i < numbers.len(),
        j < numbers.len(),
        i != j,
        abs_diff(numbers[i as int] as int, numbers[j as int] as int) < threshold as int,
    ensures
        exists|x: int, y: int| 
            0 <= x < numbers.len() && 0 <= y < numbers.len() && x != y &&
            abs_diff(numbers[x] as int, numbers[y] as int) < threshold as int,
{
}

proof fn lemma_no_close_elements(numbers: &Vec<i32>, threshold: i32)
    requires
        threshold >= 0,
        forall|i: int, j: int| 
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= threshold as int,
    ensures
        forall|x: usize, y: usize|
            x < numbers.len() && y < numbers.len() && x != y ==> 
            abs_diff(numbers[x as int] as int, numbers[y as int] as int) >= threshold as int,
{
}

proof fn lemma_safe_diff(a: i32, b: i32)
    ensures
        (a >= b ==> a - b == abs_diff(a as int, b as int)),
        (a < b ==> b - a == abs_diff(a as int, b as int)),
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
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow by using checked arithmetic */
    let mut i = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            forall|x: int, y: int|
                0 <= x < i && 0 <= y < numbers.len() && x != y ==>
                abs_diff(numbers[x] as int, numbers[y] as int) >= threshold as int,
        decreases numbers.len() - i
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                j <= numbers.len(),
                i < numbers.len(),
                forall|x: int, y: int|
                    0 <= x < i && 0 <= y < numbers.len() && x != y ==>
                    abs_diff(numbers[x] as int, numbers[y] as int) >= threshold as int,
                forall|y: int|
                    #![auto]
                    0 <= y < j && y != i as int ==>
                    abs_diff(numbers[i as int] as int, numbers[y] as int) >= threshold as int,
            decreases numbers.len() - j
        {
            if i != j {
                let val_i = numbers[i];
                let val_j = numbers[j];
                proof {
                    lemma_safe_diff(val_i, val_j);
                }
                let diff = if val_i >= val_j { 
                    (val_i as u64) - (val_j as u64)
                } else { 
                    (val_j as u64) - (val_i as u64)
                };
                if diff < threshold as u64 {
                    proof {
                        assert(abs_diff(numbers[i as int] as int, numbers[j as int] as int) < threshold as int);
                        lemma_close_elements_found(numbers, threshold, i, j);
                    }
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        lemma_no_close_elements(numbers, threshold);
    }
    false
}
// </vc-code>

}
fn main() {}