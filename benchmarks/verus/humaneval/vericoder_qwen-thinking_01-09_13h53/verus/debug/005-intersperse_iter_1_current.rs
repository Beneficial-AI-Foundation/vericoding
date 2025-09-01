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
    if numbers.is_empty() {
        return Vec::new();
    }
    let n = numbers.len();
    let mut result = Vec::with_capacity(2 * n - 1);
    for i in 0..n {
        result.push(numbers[i]);
        if i < n - 1 {
            result.push(delimiter);
        }
    }
    proof {
        assert(result@.len() == 2 * numbers.len() - 1);
        for i in 0..numbers.len() {
            assert(2 * i < result@.len());
            assert(result@.at(2 * i) == numbers@.at(i));
        }
        for i in 0..numbers.len() - 1 {
            assert(2 * i + 1 < result@.len());
            assert(result@.at(2 * i + 1) == delimiter);
        }
    }
    result
}
// </vc-code>

fn main() {}
}