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
proof fn lemma_intersperse_spec_quantified(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_spec(numbers, delimiter) == numbers || (numbers.len() > 1 && 
        intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1),
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        // Base case: result is the same as input
    } else {
        lemma_intersperse_spec_quantified(numbers.drop_last(), delimiter);
        // Recursive case: result length is 2n-1
    }
}

proof fn lemma_intersperse_properties(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)),
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        // Base case: trivial when 0 or 1 elements
    } else {
        lemma_intersperse_properties(numbers.drop_last(), delimiter);
        // Prove properties hold for recursive construction
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
    let mut result = Vec::new();
    let len = numbers.len();
    
    if len == 0 {
        return result;
    }
    
    result.push(numbers[0]);
    
    let mut i = 1;
    while i < len 
        invariant
            0 <= i <= len,
            result@.len() == 2 * i - 1,
            forall|j: int| 0 <= j < i ==> result@[even(j)] == numbers@[j],
            forall|j: int| 0 <= j < i - 1 ==> result@[odd(j)] == delimiter,
    {
        result.push(delimiter);
        result.push(numbers[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}