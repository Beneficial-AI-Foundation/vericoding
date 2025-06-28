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

// Helper lemma to prove additivity of count_less_than_in_set
proof fn lemma_count_less_than_union(set1: Set<int>, set2: Set<int>, threshold: int)
    requires set1.disjoint(set2)
    ensures count_less_than_in_set(set1.union(set2), threshold) == 
            count_less_than_in_set(set1, threshold) + count_less_than_in_set(set2, threshold)
    decreases set1.len() + set2.len()
{
    if set1.is_empty() {
        assert(set1.union(set2) == set2);
        assert(count_less_than_in_set(set1, threshold) == 0);
    } else if set2.is_empty() {
        assert(set1.union(set2) == set1);
        assert(count_less_than_in_set(set2, threshold) == 0);
    } else {
        let union = set1.union(set2);
        if !union.is_empty() {
            let elem = union.choose();
            let rest = union.remove(elem);
            
            if set1.contains(elem) {
                let set1_rest = set1.remove(elem);
                assert(rest == set1_rest.union(set2));
                assert(set1_rest.disjoint(set2));
                lemma_count_less_than_union(set1_rest, set2, threshold);
            } else {
                assert(set2.contains(elem));
                let set2_rest = set2.remove(elem);
                assert(rest == set1.union(set2_rest));
                assert(set1.disjoint(set2_rest));
                lemma_count_less_than_union(set1, set2_rest, threshold);
            }
        }
    }
}

// Helper lemma for single element sets
proof fn lemma_count_single_element(elem: int, threshold: int)
    ensures count_less_than_in_set(Set::empty().insert(elem), threshold) == 
            if elem < threshold { 1 } else { 0 }
{
    let single_set = Set::empty().insert(elem);
    assert(!single_set.is_empty());
    let chosen = single_set.choose();
    assert(chosen == elem);
    let rest = single_set.remove(chosen);
    assert(rest.is_empty());
    assert(count_less_than_in_set(rest, threshold) == 0);
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
        let new_processed = processed.insert(elem);
        
        // Prove the invariant will be maintained
        proof {
            lemma_count_single_element(elem, threshold);
            assert(Set::empty().insert(elem).disjoint(processed));
            lemma_count_less_than_union(processed, Set::empty().insert(elem), threshold);
            assert(count_less_than_in_set(new_processed, threshold) == 
                   count_less_than_in_set(processed, threshold) + 
                   count_less_than_in_set(Set::empty().insert(elem), threshold));
        }
        
        processed = new_processed;
        
        if elem < threshold {
            count = count + 1;
        }
    }
    
    // Final proof: when remaining is empty, processed contains all elements
    assert(remaining.is_empty());
    assert(processed == numbers);
    
    count
}

}