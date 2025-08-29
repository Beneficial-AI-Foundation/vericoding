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
        // Base cases
    } else {
        intersperse_spec_len(numbers.drop_last(), delimiter);
    }
}

proof fn intersperse_spec_indexing(numbers: Seq<u64>, delimiter: u64)
    requires numbers.len() > 0,
    ensures intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)),
    decreases numbers.len(),
{
    let result = intersperse_spec(numbers, delimiter);
    intersperse_spec_len(numbers, delimiter);
    
    if numbers.len() == 1 {
        // Base case: single element
        assert(result == numbers);
        assert(result.len() == 1);
        assert(result[even(0)] == result[0] == numbers[0]);
    } else {
        // Recursive case
        let sub_result = intersperse_spec(numbers.drop_last(), delimiter);
        intersperse_spec_indexing(numbers.drop_last(), delimiter);
        
        assert(result == sub_result + seq![delimiter, numbers.last()]);
        
        // Prove length property
        assert(result.len() == sub_result.len() + 2);
        assert(result.len() == 2 * numbers.drop_last().len() - 1 + 2);
        assert(result.len() == 2 * (numbers.len() - 1) - 1 + 2);
        assert(result.len() == 2 * numbers.len() - 1);
        
        // Prove indexing properties
        assert forall|i: int| 0 <= i < numbers.len() - 1 implies result[even(i)] == numbers[i] by {
            assert(result[even(i)] == sub_result[even(i)]);
            assert(sub_result[even(i)] == numbers.drop_last()[i]);
            assert(numbers.drop_last()[i] == numbers[i]);
        }
        
        // Handle last element
        let last_idx = numbers.len() - 1;
        assert(even(last_idx) == 2 * last_idx);
        assert(result[even(last_idx)] == result[(sub_result.len() + 1) as int]);
        assert(result[(sub_result.len() + 1) as int] == numbers.last());
        assert(numbers.last() == numbers[last_idx]);
        
        // Prove delimiter indexing
        assert forall|i: int| 0 <= i < numbers.len() - 2 implies result[odd(i)] == delimiter by {
            assert(result[odd(i)] == sub_result[odd(i)]);
        }
        
        if numbers.len() >= 2 {
            let delim_idx = numbers.len() - 2;
            assert(odd(delim_idx) == 2 * delim_idx + 1);
            assert(result[odd(delim_idx)] == result[sub_result.len() as int]);
            assert(result[sub_result.len() as int] == delimiter);
        }
    }
}

proof fn intersperse_spec_subrange(numbers: Seq<u64>, delimiter: u64, i: int)
    requires 0 <= i <= numbers.len(),
    ensures intersperse_spec(numbers.subrange(0, i), delimiter) == intersperse_spec(numbers.subrange(0, i), delimiter),
{
}

proof fn intersperse_spec_prefix_build(numbers: Seq<u64>, delimiter: u64, i: int, result: Seq<u64>)
    requires 
        0 < i <= numbers.len(),
        result == intersperse_spec(numbers.subrange(0, i - 1), delimiter) + (if i - 1 > 0 { seq![delimiter] } else { seq![] }) + seq![numbers[i - 1]],
    ensures result == intersperse_spec(numbers.subrange(0, i), delimiter),
    decreases i,
{
    let prefix = numbers.subrange(0, i - 1);
    let current_prefix = numbers.subrange(0, i);
    
    if i == 1 {
        assert(prefix.len() == 0);
        assert(current_prefix == seq![numbers[0]]);
        assert(intersperse_spec(prefix, delimiter) == seq![]);
        /* code modified by LLM (iteration 5): fixed chained comparison operator precedence */
        assert(result == seq![] + seq![] + seq![numbers[0]]);
        assert(result == seq![numbers[0]]);
        assert(intersperse_spec(current_prefix, delimiter) == current_prefix);
    } else {
        assert(current_prefix == prefix + seq![numbers[i - 1]]);
        assert(intersperse_spec(current_prefix, delimiter) == intersperse_spec(prefix, delimiter) + seq![delimiter, numbers[i - 1]]);
        assert(result == intersperse_spec(prefix, delimiter) + seq![delimiter] + seq![numbers[i - 1]]);
        assert(result == intersperse_spec(prefix, delimiter) + seq![delimiter, numbers[i - 1]]);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def intersperse(numbers: List[int], delimeter: int) -> List[int]"
docstring: |
Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
test_cases:
- input:
- []
- 4
expected_output: []
- input:
- [1, 2, 3]
- 4
expected_output: [1, 4, 2, 4, 3]
*/
// </vc-description>

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
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): strengthened invariant and added proof block */
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result.len() == if i == 0 { 0 } else { 2 * i - 1 },
            result@ == intersperse_spec(numbers@.subrange(0, i as int), delimiter),
        decreases numbers.len() - i,
    {
        if i > 0 {
            result.push(delimiter);
        }
        result.push(numbers[i]);
        
        /* code modified by LLM (iteration 5): fixed type cast and variable scoping issues */
        proof {
            let old_i = i as int;
            let new_i = (i + 1) as int;
            let old_result = result@.drop_last();
            let new_result = result@;
            
            if old_i == 0 {
                assert(old_result.len() == 0);
                assert(new_result == seq![numbers[0]]);
                assert(numbers@.subrange(0, new_i) == seq![numbers[0]]);
                assert(intersperse_spec(numbers@.subrange(0, new_i), delimiter) == seq![numbers[0]]);
            } else {
                let with_delim = old_result + seq![delimiter];
                assert(new_result == with_delim + seq![numbers[old_i]]);
                assert(new_result == old_result + seq![delimiter, numbers[old_i]]);
                
                intersperse_spec_prefix_build(numbers@, delimiter, new_i, new_result);
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(numbers@.subrange(0, numbers.len() as int) == numbers@);
    }
    
    result
}
// </vc-code>

}
fn main() {}