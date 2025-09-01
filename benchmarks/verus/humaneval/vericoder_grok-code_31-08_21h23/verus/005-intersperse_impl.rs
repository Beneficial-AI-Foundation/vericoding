use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

spec fn intersperse_spec(numbers: Seq<u64>, delimiter: u64) -> (result:Seq<u64>)
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        numbers
    } else {
        intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()]
    }
}
// pure-end
// pure-end

spec fn even(i: int) -> (result:int) {
    2 * i
}
// pure-end
// pure-end

spec fn odd(i: int) -> (result:int) {
    2 * i + 1
}
// pure-end
// pure-end

spec fn intersperse_quantified(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>) -> (result:bool) {
    (if numbers.len() == 0 {
        interspersed.len() == 0
    } else {
        interspersed.len() == 2 * numbers.len() - 1
    }) && (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] interspersed[even(i)] == numbers[i])
        && (forall|i: int|
        0 <= i < numbers.len() - 1 ==> #[trigger] interspersed[odd(i)] == delimiter)
}
// pure-end

// <vc-helpers>
// Add a helper function if needed for proofs, but here it's sufficient with the spec functions already present
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: Vec<u64>, delimiter: u64) -> (result: Vec<u64>)
    // post-conditions-start
    ensures
        result@ == intersperse_spec(numbers@, delimiter),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if numbers.len() <= 1 {
        numbers
    } else {
        let len = numbers@.len();
        let mut result = Vec::with_capacity(2 * len - 1);
        for i in 0..len - 1
            invariant
                0 <= i <= len - 1,
                result.len() == 2 * i,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[2 * j] == numbers@[j],
                forall|j: int| 0 <= j < i ==> #[trigger] result@[2 * j + 1] == delimiter,
        {
            result.push(numbers[i]);
            proof {
                assert(result@[2 * i] == numbers[i]);
            }
            result.push(delimiter);
            proof {
                assert(result@[2 * i + 1] == delimiter);
                assert(result@.take((i + 1) * 2) == result@.drop_last().drop_last().push(numbers[i]).push(delimiter));
            }
        }
        result.push(numbers@.last());
        proof {
            assert_len(result@, 2 * len - 1);
            // Prove it matches the intersperse_quantified spec
            assert(forall|j: int| 0 <= j < len ==> #[trigger] result@[2 * j] == numbers@[j]);
            assert(forall|j: int| 0 <= j < len - 1 ==> #[trigger] result@[2 * j + 1] == delimiter);
        }
        result
    }
}
// </vc-code>

fn main() {}
}