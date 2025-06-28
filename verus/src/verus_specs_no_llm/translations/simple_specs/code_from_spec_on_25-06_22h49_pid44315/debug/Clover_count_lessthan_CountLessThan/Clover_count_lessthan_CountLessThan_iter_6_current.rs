use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn count_less_than_in_set(numbers: Set<int>, threshold: int) -> int {
    numbers.filter(|x: int| x < threshold).len() as int
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
            count == count_less_than_in_set(numbers.difference(remaining), threshold),
            count + count_less_than_in_set(remaining, threshold) == count_less_than_in_set(numbers, threshold)
        decreases remaining.len()
    {
        let elem = remaining.choose();
        
        // Proof that choose() gives us an element in the set
        assert(remaining.contains(elem));
        
        let new_remaining = remaining.remove(elem);
        
        // Establish the relationship between old and new state
        assert(numbers.difference(remaining).union(Set::new().insert(elem)) =~= numbers.difference(new_remaining));
        
        remaining = new_remaining;
        
        if elem < threshold {
            count = count + 1;
        }
        
        // The invariant is maintained
        assert(count == count_less_than_in_set(numbers.difference(remaining), threshold));
    }
    
    // Final proof: when remaining is empty, we've processed all elements
    assert(remaining.is_empty());
    assert(numbers.difference(remaining) =~= numbers);
    assert(count == count_less_than_in_set(numbers, threshold));
    
    count
}

}