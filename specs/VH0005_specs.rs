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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}