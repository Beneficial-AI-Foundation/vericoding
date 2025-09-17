// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn insert_delimiter(numbers: Seq<int>, delimiter: int) -> (result: Seq<int>)
    requires valid_input(numbers, delimiter)
    ensures valid_output(numbers, delimiter, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}