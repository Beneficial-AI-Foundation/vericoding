use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isMax(val: int, numbers: Seq<int>) -> bool {
    // val must be in the sequence
    numbers.contains(val) &&
    // val must be greater than or equal to all elements in the sequence
    (forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= val)
}

fn max(numbers: Seq<int>) -> (result: int)
    requires
        numbers.len() > 0
    ensures
        isMax(result, numbers)
{
    let mut max_val = numbers[0];
    let mut i = 1;
    
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            numbers.contains(max_val),
            forall|j: int| 0 <= j < i ==> numbers[j] <= max_val,
            exists|k: int| 0 <= k < i && numbers[k] == max_val,
    {
        if numbers[i] > max_val {
            max_val = numbers[i];
        }
        
        // Prove the invariant will hold for the next iteration
        assert(forall|j: int| 0 <= j <= i ==> numbers[j] <= max_val) by {
            // For all elements up to i, they're <= max_val
            assert(forall|j: int| 0 <= j < i ==> numbers[j] <= max_val); // from invariant
            assert(numbers[i] <= max_val); // from the if-else logic above
        };
        
        i = i + 1;
        
        // Help maintain the invariants
        assert(numbers.contains(max_val));
        assert(exists|k: int| 0 <= k < i && numbers[k] == max_val);
        assert(forall|j: int| 0 <= j < i ==> numbers[j] <= max_val);
    }
    
    // After the loop, establish the postcondition
    assert(i == numbers.len());
    assert(forall|j: int| 0 <= j < numbers.len() ==> numbers[j] <= max_val);
    assert(numbers.contains(max_val));
    assert(isMax(max_val, numbers));
    
    max_val
}

}