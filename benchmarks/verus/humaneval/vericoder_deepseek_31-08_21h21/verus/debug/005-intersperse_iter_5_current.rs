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
        if numbers.len() == 0 {
            assert(intersperse_spec(numbers, delimiter).len() == 0);
        } else {
            assert(intersperse_spec(numbers, delimiter).len() == 1);
            assert(intersperse_spec(numbers, delimiter)@[even(0)] == numbers@[0]);
        }
    } else {
        lemma_intersperse_properties(numbers.drop_last(), delimiter);
        let rec_result = intersperse_spec(numbers.drop_last(), delimiter);
        let full_result = rec_result + seq![delimiter, numbers.last()];
        
        assert(full_result.len() == rec_result.len() + 2) by {
            assert(rec_result.len() == 2 * numbers.drop_last().len() - 1);
            assert(numbers.drop_last().len() == numbers.len() - 1);
        };
        
        // Prove element properties
        forall|j: int| 0 <= j < numbers.len() - 1 ==> {
            assert(full_result@[even(j)] == rec_result@[even(j)]);
            assert(rec_result@[even(j)] == numbers.drop_last()@[j]);
            assert(numbers.drop_last()@[j] == numbers@[j]);
        };
        
        assert(full_result@[even(numbers.len() - 1)] == numbers.last());
        
        forall|j: int| 0 <= j < numbers.len() - 1 ==> {
            assert(full_result@[odd(j)] == rec_result@[odd(j)]);
            assert(rec_result@[odd(j)] == delimiter);
        };
    }
}

proof fn lemma_even_odd_properties()
    ensures
        forall|i: int| 0 <= i ==> even(i) >= 0 && odd(i) >= 0,
        forall|i: int| 0 <= i ==> even(i) % 2 == 0 && odd(i) % 2 == 1,
{
    // These properties are fundamental to even/odd definitions
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
            forall|j: int| 0 <= j < i ==> result@[2 * j] == numbers@[j],
            forall|j: int| 0 <= j < i - 1 ==> result@[2 * j + 1] == delimiter,
    {
        result.push(delimiter);
        result.push(numbers[i]);
        i += 1;
        
        proof {
            assert forall|j: int| 0 <= j < i implies result@[2 * j] == numbers@[j] by {
                if j < old(i) {
                    assert(result@[2 * j] == old(result)@[2 * j]);
                } else if j == i - 1 {
                    assert(result@[2 * j] == numbers@[j]);
                }
            };
            
            assert forall|j: int| 0 <= j < i - 1 implies result@[2 * j + 1] == delimiter by {
                if j < old(i) - 1 {
                    assert(result@[2 * j + 1] == old(result)@[2 * j + 1]);
                } else if j == i - 2 {
                    assert(result@[2 * j + 1] == delimiter);
                }
            };
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}