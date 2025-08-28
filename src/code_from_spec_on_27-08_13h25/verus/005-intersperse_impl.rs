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
proof fn intersperse_spec_len(numbers: Seq<u64>, delimiter: u64)
    ensures
        numbers.len() > 0 ==> intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1,
    decreases numbers.len(),
{
    if numbers.len() > 0 {
        intersperse_spec_len(numbers.drop_last(), delimiter);
    }
}

proof fn intersperse_quantified_is_spec(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>)
    requires
        intersperse_quantified(numbers, delimiter, interspersed),
    ensures
        interspersed == intersperse_spec(numbers, delimiter),
    decreases numbers.len(),
{
    let is = intersperse_spec(numbers, delimiter);
    if numbers.len() == 0 {
    } else if numbers.len() == 1 {
        assert(interspersed.len() == 1);
        assert(interspersed[even(0)] == numbers[0]);
    } else {
        intersperse_quantified_is_spec(
            numbers.drop_last(),
            delimiter,
            interspersed.take(interspersed.len() - 2),
        );
        intersperse_spec_len(numbers, delimiter);
        assert_seqs_equal!(is == interspersed, i => {
            if i < is.len() - 2 {
            } else {
                if i % 2 == 0 {
                    assert(is[i] == numbers.last());
                    assert(interspersed[even(i/2)] == numbers[i / 2]);
                    assert(i / 2 == numbers.len() - 1);
                } else {
                    assert(is[i] == delimiter);
                    assert(interspersed[odd((i-1)/2)] == delimiter);
                }
            }
        });
    }
    assert(interspersed =~= intersperse_spec(numbers, delimiter));
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
fn intersperse(numbers: Vec<u64>, delimiter: u64) -> (result: Vec<u64>)
    ensures
        result@ == intersperse_spec(numbers@, delimiter),
{
    let mut result: Vec<u64> = Vec::new();
    let len = numbers.len();
    if len == 0 {
        return result;
    }
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result@.len() == if i == 0 { 0 } else { 2 * i - 1 },
            forall|j: int| 0 <= j < i ==> result@[even(j as int)] == numbers@[j],
            forall|j: int| 0 <= j < i - 1 ==> result@[odd(j as int)] == delimiter,
    {
        result.push(numbers[i]);
        if i < len - 1 {
            result.push(delimiter);
        }
        i = i + 1;
    }
    proof {
        intersperse_spec_len(numbers@, delimiter);
        assert(intersperse_quantified(numbers@, delimiter, result@));
        intersperse_quantified_is_spec(numbers@, delimiter, result@);
    }
    result
}
// </vc-code>

}
fn main() {}