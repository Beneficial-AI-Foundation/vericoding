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

// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Vec<i8>, threshold: i8) -> (result: bool)
    requires valid_input(seq_map_to_int(numbers@), threshold as int)
    ensures result == has_close_elements(seq_map_to_int(numbers@), threshold as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [changed condition from ghost to exec mode, changed ghost threshold_val to exec `let threshold_concrete = threshold as int;` ] */
{
    let n = numbers.len();
    let threshold_concrete = threshold as int;

    if n == 0 || n == 1 {
        return false;
    }

    let ghost numbers_seq = numbers@.map(|_i, x| x as int);

    let mut i: usize = 0;
    while i < n - 1
        invariant
            0 <= i,
            i <= n - 1,
            forall|k: int, l: int| #![auto] 0 <= k < l < i as int ==> abs_diff(numbers_seq[k], numbers_seq[l]) >= threshold_concrete,
            numbers_seq == numbers@.map(|_j, x| x as int),
            threshold_concrete == threshold as int,
            n == numbers.len()
        decreases n - 1 - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= i,
                i < j,
                j <= n,
                forall|k: int, l: int| #![auto] 0 <= k < l < i as int ==> abs_diff(numbers_seq[k], numbers_seq[l]) >= threshold_concrete,
                forall|l: int| #![auto] (i as int) < l && l < (j as int) ==> abs_diff(numbers_seq[i as int], numbers_seq[l]) >= threshold_concrete,
                numbers_seq == numbers@.map(|_idx, x| x as int),
                threshold_concrete == threshold as int,
                n == numbers.len()
            decreases n - j
        {
            let diff_val = abs_diff(numbers_seq[i as int], numbers_seq[j as int]);
            if diff_val < threshold_concrete {
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