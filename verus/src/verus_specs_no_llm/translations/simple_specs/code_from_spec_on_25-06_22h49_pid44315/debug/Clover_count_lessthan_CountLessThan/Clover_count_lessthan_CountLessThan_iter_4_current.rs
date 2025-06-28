use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn count_less_than_in_set(numbers: Set<int>, threshold: int) -> int
    decreases numbers.finite_len()
{
    if numbers.is_empty() {
        0
    } else {
        let elem = numbers.choose();
        let rest = numbers.remove(elem);
        count_less_than_in_set(rest, threshold) + if elem < threshold { 1 } else { 0 }
    }
}

// Helper lemma to establish the recursive relationship
proof fn lemma_count_decomposition(numbers: Set<int>, threshold: int, elem: int)
    requires numbers.contains(elem)
    ensures count_less_than_in_set(numbers, threshold) == 
            count_less_than_in_set(numbers.remove(elem), threshold) + if elem < threshold { 1 } else { 0 }
    decreases numbers.finite_len()
{
    if numbers.finite_len() == 1 {
        assert(numbers =~= Set::new().insert(elem));
        assert(numbers.remove(elem) =~= Set::new());
    } else {
        let chosen = numbers.choose();
        if chosen == elem {
            // The recursive definition already gives us what we want
        } else {
            // We need to show the decomposition works for a different element
            let rest_with_elem = numbers.remove(chosen);
            let rest_without_elem = numbers.remove(chosen).remove(elem);
            
            assert(rest_with_elem.contains(elem));
            lemma_count_decomposition(rest_with_elem, threshold, elem);
            
            assert(numbers.remove(elem).remove(chosen) =~= rest_without_elem);
        }
    }
}

fn CountLessThan(numbers: Set<int>, threshold: int) -> (count: int)
    ensures
        count == count_less_than_in_set(numbers, threshold)
{
    let mut count = 0;
    let mut remaining = numbers;
    
    while remaining.finite_len() > 0
        invariant
            remaining.subset_of(numbers),
            count + count_less_than_in_set(remaining, threshold) == count_less_than_in_set(numbers, threshold)
        decreases remaining.finite_len()
    {
        let elem = remaining.choose();
        
        // Proof that choose() gives us an element in the set
        assert(remaining.contains(elem));
        
        // Use the lemma to establish the recursive relationship
        lemma_count_decomposition(remaining, threshold, elem);
        
        remaining = remaining.remove(elem);
        
        if elem < threshold {
            count = count + 1;
        }
        
        // The invariant is maintained by the lemma
        assert(count + count_less_than_in_set(remaining, threshold) == count_less_than_in_set(numbers, threshold));
    }
    
    // Final proof that empty set has count 0
    assert(count_less_than_in_set(remaining, threshold) == 0);
    
    count
}

}