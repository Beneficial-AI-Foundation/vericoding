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
            exists|k: int| 0 <= k < i && numbers[k] == max_val
    {
        if numbers[i] > max_val {
            max_val = numbers[i];
        }
        i = i + 1;
    }
    
    // After the loop, i == numbers.len(), so the invariant gives us
    // forall|j: int| 0 <= j < numbers.len() ==> numbers[j] <= max_val
    assert(i == numbers.len());
    assert(forall|j: int| 0 <= j < numbers.len() ==> numbers[j] <= max_val);
    assert(numbers.contains(max_val));
    
    max_val
}

}