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
            
            // Proof that the new max_val maintains the invariant
            assert(numbers.contains(max_val));
            assert(forall|j: int| 0 <= j < i ==> numbers[j] <= max_val) by {
                assert(forall|j: int| 0 <= j < i ==> numbers[j] <= numbers[0]);
                assert(forall|j: int| 0 <= j < i ==> numbers[j] <= max_val);
            };
            assert(numbers[i] == max_val);
        }
        
        i = i + 1;
        
        // Proof that incrementing i maintains the invariant
        assert(forall|j: int| 0 <= j < i ==> numbers[j] <= max_val) by {
            if i > 1 {
                assert(forall|j: int| 0 <= j < i - 1 ==> numbers[j] <= max_val);
                assert(numbers[i - 1] <= max_val);
            }
        };
    }
    
    // Final proof that isMax holds
    assert(forall|j: int| 0 <= j < numbers.len() ==> numbers[j] <= max_val) by {
        assert(i == numbers.len());
        assert(forall|j: int| 0 <= j < i ==> numbers[j] <= max_val);
    };
    
    max_val
}

}