use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to recursively build the interspersed sequence
spec fn intersperse_helper(numbers: Seq<int>, delimiter: int, index: nat) -> Seq<int>
    decreases numbers.len() - index
{
    if index >= numbers.len() {
        Seq::empty()
    } else if index == numbers.len() - 1 {
        seq![numbers[index as int]]
    } else {
        seq![numbers[index as int], delimiter] + intersperse_helper(numbers, delimiter, index + 1)
    }
}

// Lemma to prove properties about the helper function
proof fn intersperse_helper_properties(numbers: Seq<int>, delimiter: int, index: nat)
    requires index <= numbers.len()
    ensures ({
        let result = intersperse_helper(numbers, delimiter, index);
        // Length property
        result.len() == if index >= numbers.len() { 0 } 
                       else if index == numbers.len() - 1 { 1 }
                       else { 2 * (numbers.len() - index) - 1 }
    })
    decreases numbers.len() - index
{
    if index >= numbers.len() {
        // Base case: empty
    } else if index == numbers.len() - 1 {
        // Base case: single element
    } else {
        // Recursive case
        intersperse_helper_properties(numbers, delimiter, index + 1);
    }
}

// Main lemma to prove the intersperse properties
proof fn intersperse_correct(numbers: Seq<int>, delimiter: int, result: Seq<int>)
    requires 
        result == if numbers.len() == 0 { Seq::empty() } else { intersperse_helper(numbers, delimiter, 0) }
    ensures
        result.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < result.len() && i % 2 == 0 ==> 
            #[trigger] result[i] == numbers[i / 2],
        forall|i: int| 0 <= i < result.len() && i % 2 == 1 ==>
            #[trigger] result[i] == delimiter,
{
    if numbers.len() == 0 {
        // Empty case is trivial
    } else {
        intersperse_helper_properties(numbers, delimiter, 0);
        intersperse_indices(numbers, delimiter, 0);
    }
}

// Prove index mapping properties
proof fn intersperse_indices(numbers: Seq<int>, delimiter: int, start: nat)
    requires start <= numbers.len()
    ensures 
        ({
            let result = intersperse_helper(numbers, delimiter, start);
            (forall|i: int| 0 <= i < result.len() && i % 2 == 0 ==> 
                #[trigger] result[i] == numbers[start + i / 2])
            &&
            (forall|i: int| 0 <= i < result.len() && i % 2 == 1 ==>
                #[trigger] result[i] == delimiter)
        })
    decreases numbers.len() - start
{
    if start >= numbers.len() {
        // Empty case
    } else if start == numbers.len() - 1 {
        // Single element case
        assert(intersperse_helper(numbers, delimiter, start).len() == 1);
    } else {
        // Recursive case
        let prefix = seq![numbers[start as int], delimiter];
        let suffix = intersperse_helper(numbers, delimiter, start + 1);
        let result = prefix + suffix;
        
        intersperse_indices(numbers, delimiter, start + 1);
        
        assert forall|i: int| 0 <= i < result.len() && i % 2 == 0 implies
            #[trigger] result[i] == numbers[start + i / 2] by {
            if i == 0 {
                assert(result[0] == prefix[0]);
                assert(prefix[0] == numbers[start as int]);
            } else {
                assert(i >= 2);
                assert(result[i] == suffix[i - 2]);
                assert(suffix[i - 2] == numbers[start + 1 + (i - 2) / 2]);
                assert(start + i / 2 == start + 1 + (i - 2) / 2);
            }
        }
        
        assert forall|i: int| 0 <= i < result.len() && i % 2 == 1 implies
            #[trigger] result[i] == delimiter by {
            if i == 1 {
                assert(result[1] == prefix[1]);
                assert(prefix[1] == delimiter);
            } else {
                assert(i >= 3);
                assert(result[i] == suffix[i - 2]);
                assert(suffix[i - 2] == delimiter);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
proof fn intersperse(numbers: Seq<int>, delimiter: int) -> (interspersed: Seq<int>)
    ensures
        interspersed.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 0 ==> 
            interspersed[i] == numbers[i / 2],
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 1 ==>
            interspersed[i] == delimiter,
// </vc-spec>
// <vc-code>
{
    let interspersed = if numbers.len() == 0 {
        Seq::empty()
    } else {
        intersperse_helper(numbers, delimiter, 0)
    };
    
    intersperse_correct(numbers, delimiter, interspersed);
    
    interspersed
}
// </vc-code>

fn main() {}

}