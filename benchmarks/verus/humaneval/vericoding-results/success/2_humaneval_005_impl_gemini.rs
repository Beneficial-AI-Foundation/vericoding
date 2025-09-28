// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(numbers: Seq<int>, delimiter: int) -> bool {
        true /* Any sequence and delimiter are valid inputs */
}
    
spec fn valid_output(numbers: Seq<int>, delimiter: int, result: Seq<int>) -> bool {
        if numbers.len() <= 1 {
            result == numbers
        } else {
            result.len() == 2 * numbers.len() - 1 &&
            (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] result[2 * i] == numbers[i]) &&
            (forall|i: int| 0 <= i < numbers.len() - 1 ==> #[trigger] result[2 * i + 1] == delimiter)
        }
}
    
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insert_delimiter(numbers: Vec<i8>, delimiter: i8) -> (result: Vec<i8>)
    requires valid_input(numbers@.map(|_i: int, x: i8| x as int), delimiter as int)
    ensures valid_output(numbers@.map(|_i: int, x: i8| x as int), delimiter as int, result@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed 'let' statement compilation error in invariant */
    let n_len = numbers.len();
    if n_len <= 1 {
        return numbers;
    }

    let mut result: Vec<i8> = Vec::new();
    result.push(numbers[0]);

    let mut i: usize = 1;
    while i < n_len
        invariant
            n_len > 1,
            1 <= i <= n_len,
            numbers.len() == n_len,
            result.len() == 2 * i - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] (result@[2 * j] as int) == (numbers@[j] as int),
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] (result@[2 * j + 1] as int) == (delimiter as int),
        decreases n_len - i
    {
        result.push(delimiter);
        result.push(numbers[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}