// <vc-preamble>
use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)

    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fix type error in invariant */
{
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            forall|k: int, l: int| 0 <= k < (i as int) && k < l < (numbers@.len() as int) ==> abs((numbers@[k] - numbers@[l]) as int) >= threshold as int,
        decreases numbers.len() - i
    {
        let mut j: usize = i + 1;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                i < j <= numbers.len(),
                forall|k: int, l: int| 0 <= k < (i as int) && k < l < (numbers@.len() as int) ==> abs((numbers@[k] - numbers@[l]) as int) >= threshold as int,
                forall|l: int| (i as int) < l < (j as int) ==> abs((numbers@[i as int] - numbers@[l]) as int) >= threshold as int,
            decreases numbers.len() - j
        {
            let a = numbers[i];
            let b = numbers[j];
            let diff = if a > b { 
                let res = a.checked_sub(b);
                if res.is_none() { false } else { res.unwrap() < threshold }
            } else {
                let res = b.checked_sub(a);
                if res.is_none() { false } else { res.unwrap() < threshold }
            };

            if diff {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}