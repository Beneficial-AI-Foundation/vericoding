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
        count_less_than_in_set(rest, threshold) + if elem < threshold { 1 } else { 0 }
    }
}

fn CountLessThan(numbers: Set<int>, threshold: int) -> (count: int)
    ensures
        count == count_less_than_in_set(numbers, threshold)
{
    let mut count = 0;
    let mut remaining = numbers;
    
    while remaining.len() > 0
        invariant
            remaining.subset_of(numbers),
            count + count_less_than_in_set(remaining, threshold) == count_less_than_in_set(numbers, threshold)
        decreases remaining.len()
    {
        let elem = remaining.choose();
        
        // Proof that choose() gives us an element in the set
        assert(remaining.contains(elem));
        
        remaining = remaining.remove(elem);
        
        // Proof about the recursive relationship
        assert(count_less_than_in_set(numbers.insert(elem), threshold) == 
               count_less_than_in_set(numbers, threshold) + if elem < threshold { 1 } else { 0 });
        
        if elem < threshold {
            count = count + 1;
        }
        
        // Help the verifier understand the invariant preservation
        assert(count + count_less_than_in_set(remaining, threshold) == count_less_than_in_set(numbers, threshold));
    }
    
    // Final proof that empty set has count 0
    assert(count_less_than_in_set(remaining, threshold) == 0);
    
    count
}

}