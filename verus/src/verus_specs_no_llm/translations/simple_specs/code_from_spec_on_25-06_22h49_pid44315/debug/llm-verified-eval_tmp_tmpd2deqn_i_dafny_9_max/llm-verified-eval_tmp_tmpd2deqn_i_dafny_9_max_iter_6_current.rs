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
            0 < i <= numbers.len(),
            numbers.contains(max_val),
            forall|j: int| 0 <= j < i ==> numbers[j] <= max_val,
            exists|k: int| 0 <= k < i && numbers[k] == max_val,
    {
        if numbers[i] > max_val {
            max_val = numbers[i];
        }
        i = i + 1;
    }
    
    // After the loop, we need to establish that max_val >= all elements
    // The invariant tells us max_val >= all elements from 0 to i-1
    // Since i == numbers.len() after the loop, this covers all elements
    assert(i == numbers.len());
    assert(forall|j: int| 0 <= j < numbers.len() ==> numbers[j] <= max_val);
    assert(numbers.contains(max_val));
    
    max_val
}

}