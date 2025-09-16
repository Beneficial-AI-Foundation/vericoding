// <vc-preamble>
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

spec fn even(i: int) -> (result:int) {
    2 * i
}

spec fn odd(i: int) -> (result:int) {
    2 * i + 1
}

spec fn intersperse_quantified(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>) -> (result:bool) {
    (if numbers.len() == 0 {
        interspersed.len() == 0
    } else {
        interspersed.len() == 2 * numbers.len() - 1
    }) && (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] interspersed[even(i)] == numbers[i])
        && (forall|i: int|
        0 <= i < numbers.len() - 1 ==> #[trigger] interspersed[odd(i)] == delimiter)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): implemented proof for lemma */
proof fn intersperse_spec_unfold(numbers: Seq<u64>, delimiter: u64, i: int)
    requires
        1 <= i < numbers.len(),
    ensures
        intersperse_spec(numbers.take(i + 1), delimiter) ==
            intersperse_spec(numbers.take(i), delimiter) + seq![delimiter, numbers[i]],
{
    let s = numbers.take(i + 1);
    assert(s.len() > 1);
    assert(intersperse_spec(s, delimiter) == intersperse_spec(s.drop_last(), delimiter) + seq![delimiter, s.last()]);
    assert(s.drop_last() == numbers.take(i));
    assert(s.last() == numbers[i]);
}
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: Vec<u64>, delimiter: u64) -> (result: Vec<u64>)

    ensures
        result@ == intersperse_spec(numbers@, delimiter),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): logic is correct, relying on fixed helper lemma */
    let mut result: Vec<u64> = Vec::new();
    let n = numbers.len();
    if n == 0 {
        return result;
    }

    result.push(numbers[0]);

    let mut i: usize = 1;
    while i < n
        invariant
            n == numbers.len(),
            1 <= i <= n,
            result@ == intersperse_spec(numbers@.take(i as int), delimiter),
        decreases n - i
    {
        result.push(delimiter);
        result.push(numbers[i]);

        proof {
            intersperse_spec_unfold(numbers@, delimiter, i as int);
        }

        i = i + 1;
    }

    assert(result@ == intersperse_spec(numbers@.take(n as int), delimiter));
    assert(numbers@.take(n as int) == numbers@);

    result
}
// </vc-code>

}
fn main() {}