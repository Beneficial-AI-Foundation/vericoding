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
    if numbers.len() <= 1 {
        numbers
    } else {
        let len = numbers.len();
        let last = numbers[len - 1];
        let mut prefix_vec = Vec::new();
        for i in 0..len - 1
            invariant
                0 <= i <= len - 1,
                prefix_vec.len() == i as usize,
                prefix_vec@ == numbers@.subrange(0, i as int),
        {
            proof {
                assert(prefix_vec@.len() == i);
            }
            prefix_vec.push(numbers[i]);
        }
        let mut inter = intersperse(prefix_vec, delimiter);
        assert(inter@ == intersperse_spec(numbers@.subrange(0, len - 1), delimiter));
        assert(intersperse_spec(numbers@, delimiter) =~= inter@ + seq![delimiter, last]);
        inter.push(delimiter);
        inter.push(last);
        inter
    }
}
// </vc-code>

fn main() {}
}