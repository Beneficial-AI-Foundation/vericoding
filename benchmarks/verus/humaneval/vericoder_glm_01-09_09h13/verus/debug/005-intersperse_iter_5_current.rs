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
proof fn lemma_intersperse_quantified_equivalence(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)),
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        assert(numbers == intersperse_spec(numbers, delimiter));
        if numbers.len() == 0nat {
            assert(intersperse_spec(numbers, delimiter).len() == 0);
        } else {
            assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1);
            assert(forall|i: int| 0 <= i < numbers.len() ==> #[trigger] intersperse_spec(numbers, delimiter)[even(i)] == numbers[i]);
            assert(forall|i: int| 0 <= i < numbers.len() - 1 ==> #[trigger] intersperse_spec(numbers, delimiter)[odd(i)] == delimiter);
        }
    } else {
        lemma_intersperse_quantified_equivalence(numbers.drop_last(), delimiter);
        let dropped_len = numbers.drop_last().len();
        assert(intersperse_spec(numbers, delimiter) == intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()]);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1);
        assert(forall|i: int| 0 <= i < dropped_len ==> #[trigger] intersperse_spec(numbers.drop_last(), delimiter)[even(i)] == numbers.drop_last()[i]);
        assert(intersperse_spec(numbers, delimiter)[even(dropped_len as int)] == numbers.last());
        assert(forall|i: int| 0 <= i < dropped_len - 1 ==> #[trigger] intersperse_spec(numbers.drop_last(), delimiter)[odd(i)] == delimiter);
        assert(intersperse_spec(numbers, delimiter)[odd(dropped_len - 1)] == delimiter);
    }
}

fn intersperse_seq_helper(numbers: Seq<u64>, delimiter: u64) -> (result: Seq<u64>)
    ensures result == intersperse_spec(numbers, delimiter),
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        numbers
    } else {
        let prefix = intersperse_seq_helper(numbers.drop_last(), delimiter);
        prefix.push(delimiter).push(numbers.last())
    }
}
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
    if numbers
// </vc-code>

fn main() {}
}