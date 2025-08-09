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

spec fn even(i: int) -> (result:int) {
    2 * i
}
// pure-end

spec fn odd(i: int) -> (result:int) {
    2 * i + 1
}
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

proof fn intersperse_spec_len(numbers: Seq<u64>, delimiter: u64)
    // post-conditions-start
    ensures
        numbers.len() > 0 ==> intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1,
    decreases numbers.len(),
    // post-conditions-end
{
    if numbers.len() > 1 {
        intersperse_spec_len(numbers.drop_last(), delimiter);
    }
}
// pure-end

proof fn intersperse_quantified_is_spec(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>)
    // pre-conditions-start
    requires
        intersperse_quantified(numbers, delimiter, interspersed),
    // pre-conditions-end
    // post-conditions-start
    ensures
        interspersed == intersperse_spec(numbers, delimiter),
    decreases numbers.len(),
    // post-conditions-end
{
    if numbers.len() == 0 {
        // Base case: empty sequence
    } else if numbers.len() == 1 {
        // Base case: single element
        assert(interspersed.len() == 1);
        assert(interspersed[0] == numbers[0]);
        assert(interspersed == numbers);
        assert(intersperse_spec(numbers, delimiter) == numbers);
    } else {
        // Recursive case
        let prefix = numbers.drop_last();
        let interspersed_prefix = interspersed.take(interspersed.len() - 2);
        
        // Show that prefix satisfies the quantified property
        assert forall|i: int| 0 <= i < prefix.len() implies #[trigger] interspersed_prefix[even(i)] == prefix[i] by {
            assert(interspersed_prefix[even(i)] == interspersed[even(i)]);
            assert(interspersed[even(i)] == numbers[i]);
            assert(numbers[i] == prefix[i]);
        }
        
        assert forall|i: int| 0 <= i < prefix.len() - 1 implies #[trigger] interspersed_prefix[odd(i)] == delimiter by {
            assert(interspersed_prefix[odd(i)] == interspersed[odd(i)]);
            assert(interspersed[odd(i)] == delimiter);
        }
        
        assert(intersperse_quantified(prefix, delimiter, interspersed_prefix));
        intersperse_quantified_is_spec(prefix, delimiter, interspersed_prefix);
        
        // Show the recursive relationship
        let spec_prefix = intersperse_spec(prefix, delimiter);
        assert(interspersed_prefix == spec_prefix);
        
        let last_two = interspersed.skip(interspersed.len() - 2);
        assert(last_two.len() == 2);
        assert(last_two[0] == delimiter);
        assert(last_two[1] == numbers.last());
        assert(last_two == seq![delimiter, numbers.last()]);
        
        assert(interspersed == interspersed_prefix + last_two);
        assert(interspersed == spec_prefix + seq![delimiter, numbers.last()]);
        assert(interspersed == intersperse_spec(numbers, delimiter));
    }
}
// pure-end

fn intersperse(numbers: Vec<u64>, delimiter: u64) -> (result: Vec<u64>)
    // post-conditions-start
    ensures
        result@ == intersperse_spec(numbers@, delimiter),
    // post-conditions-end
{
    let mut result = Vec::new();
    
    if numbers.len() == 0 {
        return result;
    }
    
    result.push(numbers[0]);
    
    let mut i = 1;
    /* code modified by LLM (iteration 1): Added decreases clause to fix termination error */
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            result.len() == 2 * i - 1,
            result@ == intersperse_spec(numbers@.take(i as int), delimiter),
        decreases numbers.len() - i,
    {
        result.push(delimiter);
        result.push(numbers[i]);
        
        proof {
            /* code modified by LLM (iteration 1): Fixed type mismatches by casting usize to int for Vec indexing */
            let take_i = numbers@.take(i as int);
            let take_i_plus_1 = numbers@.take((i + 1) as int);
            assert(take_i_plus_1 == take_i + seq![numbers[i as int]]);
            assert(take_i_plus_1.drop_last() == take_i);
            assert(take_i_plus_1.last() == numbers[i as int]);
            
            let expected = intersperse_spec(take_i_plus_1, delimiter);
            assert(expected == intersperse_spec(take_i, delimiter) + seq![delimiter, numbers[i as int]]);
        }
        
        i += 1;
    }
    
    proof {
        assert(numbers@.take(numbers.len() as int) == numbers@);
    }
    
    result
}

}
fn main() {}