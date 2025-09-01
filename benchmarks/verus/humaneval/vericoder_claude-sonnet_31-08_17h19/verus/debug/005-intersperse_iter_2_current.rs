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
        numbers.len() == 0 ==> intersperse_spec(numbers, delimiter).len() == 0,
        numbers.len() > 0 ==> intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1,
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
    } else {
        intersperse_spec_len(numbers.drop_last(), delimiter);
    }
}

proof fn intersperse_spec_indexing(numbers: Seq<u64>, delimiter: u64)
    requires numbers.len() > 0,
    ensures
        forall|i: int| 0 <= i < numbers.len() ==> #[trigger] intersperse_spec(numbers, delimiter)[even(i)] == numbers[i],
        forall|i: int| 0 <= i < numbers.len() - 1 ==> #[trigger] intersperse_spec(numbers, delimiter)[odd(i)] == delimiter,
    decreases numbers.len(),
{
    intersperse_spec_len(numbers, delimiter);
    if numbers.len() == 1 {
    } else {
        intersperse_spec_indexing(numbers.drop_last(), delimiter);
        let spec_result = intersperse_spec(numbers, delimiter);
        let spec_prefix = intersperse_spec(numbers.drop_last(), delimiter);
        
        assert forall|i: int| 0 <= i < numbers.len() implies #[trigger] spec_result[even(i)] == numbers[i] by {
            if i < numbers.len() - 1 {
                assert(spec_result[even(i)] == spec_prefix[even(i)]);
                assert(spec_prefix[even(i)] == numbers.drop_last()[i]);
                assert(numbers.drop_last()[i] == numbers[i]);
            } else {
                assert(i == numbers.len() - 1);
                assert(even(i) == 2 * (numbers.len() - 1));
                assert(spec_result[even(i)] == numbers.last());
                assert(numbers.last() == numbers[i]);
            }
        }
        
        assert forall|i: int| 0 <= i < numbers.len() - 1 implies #[trigger] spec_result[odd(i)] == delimiter by {
            if i < numbers.len() - 2 {
                assert(spec_result[odd(i)] == spec_prefix[odd(i)]);
                assert(spec_prefix[odd(i)] == delimiter);
            } else {
                assert(i == numbers.len() - 2);
                assert(odd(i) == 2 * (numbers.len() - 2) + 1 == 2 * numbers.len() - 3);
                assert(spec_result[odd(i)] == delimiter);
            }
        }
    }
}

proof fn intersperse_loop_establishes_spec(numbers: Seq<u64>, delimiter: u64, result: Seq<u64>, n: int)
    requires
        numbers.len() > 0,
        n == numbers.len(),
        result.len() == 2 * n - 1,
        forall|j: int| 0 <= j < n ==> #[trigger] result[even(j)] == numbers[j],
        forall|j: int| 0 <= j < n - 1 ==> #[trigger] result[odd(j)] == delimiter,
    ensures
        result == intersperse_spec(numbers, delimiter),
{
    intersperse_spec_len(numbers, delimiter);
    intersperse_spec_indexing(numbers, delimiter);
    
    let spec_result = intersperse_spec(numbers, delimiter);
    
    assert(result.len() == spec_result.len());
    
    assert forall|k: int| 0 <= k < result.len() implies result[k] == spec_result[k] by {
        if k % 2 == 0 {
            let j = k / 2;
            assert(k == even(j));
            assert(0 <= j < n);
            assert(result[k] == numbers[j]);
            assert(spec_result[k] == numbers[j]);
        } else {
            let j = k / 2;
            assert(k == odd(j));
            assert(0 <= j < n - 1);
            assert(result[k] == delimiter);
            assert(spec_result[k] == delimiter);
        }
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
    if numbers.len() == 0 {
        return vec![];
    }
    
    let mut result = Vec::new();
    
    for i in 0..numbers.len()
        invariant
            result.len() == if i == 0 { 0 } else { 2 * i - 1 },
            forall|j: int| 0 <= j < i ==> #[trigger] result@[even(j)] == numbers@[j],
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] result@[odd(j)] == delimiter,
    {
        if i > 0 {
            result.push(delimiter);
        }
        result.push(numbers[i]);
    }
    
    proof {
        intersperse_loop_establishes_spec(numbers@, delimiter, result@, numbers.len() as int);
    }
    
    result
}
// </vc-code>

fn main() {}
}