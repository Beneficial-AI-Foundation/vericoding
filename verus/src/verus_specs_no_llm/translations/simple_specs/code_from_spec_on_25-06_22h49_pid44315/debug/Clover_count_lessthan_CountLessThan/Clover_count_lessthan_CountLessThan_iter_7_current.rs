use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn count_less_than_in_set(numbers: Set<int>, threshold: int) -> int
    decreases numbers.len()
{
    if numbers.is_empty() {
        0
    } else {
        let elem = numbers.choose();
        let rest = numbers.remove(elem);
        let count_rest = count_less_than_in_set(rest, threshold);
        if elem < threshold {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

fn CountLessThan(numbers: Set<int>, threshold: int) -> (count: int)
    ensures
        count == count_less_than_in_set(numbers, threshold)
{
    let mut count = 0;
    let mut remaining = numbers;
    let mut processed = Set::<int>::empty();
    
    while remaining.len() > 0
        invariant
            remaining.disjoint(processed),
            remaining.union(processed) == numbers,
            count == count_less_than_in_set(processed, threshold)
        decreases remaining.len()
    {
        let elem = remaining.choose();
        
        // Remove element from remaining and add to processed
        remaining = remaining.remove(elem);
        processed = processed.insert(elem);
        
        if elem < threshold {
            count = count + 1;
        }
    }
    
    // Final proof: when remaining is empty, processed contains all elements
    assert(remaining.is_empty());
    assert(processed == numbers);
    assert(count == count_less_than_in_set(numbers, threshold));
    
    count
}

}