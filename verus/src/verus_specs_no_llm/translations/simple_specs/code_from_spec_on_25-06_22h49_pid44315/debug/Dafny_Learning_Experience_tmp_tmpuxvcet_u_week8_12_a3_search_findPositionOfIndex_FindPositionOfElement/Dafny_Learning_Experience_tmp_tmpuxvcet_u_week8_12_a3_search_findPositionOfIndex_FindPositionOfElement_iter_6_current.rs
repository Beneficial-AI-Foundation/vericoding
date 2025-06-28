use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to count occurrences
spec fn count_occurrences(s: Seq<int>, element: nat, end: int) -> nat
    decreases end
{
    if end <= 0 {
        0
    } else {
        count_occurrences(s, element, end - 1) + 
        if s.spec_index((end - 1) as int) == element { 1 } else { 0 }
    }
}

// Lemma to help with count verification
proof fn lemma_count_increment(s: Seq<int>, element: nat, i: int)
    requires i >= 0
    ensures 
        s.spec_index(i) == element ==> 
            count_occurrences(s, element, i + 1) == count_occurrences(s, element, i) + 1,
        s.spec_index(i) != element ==> 
            count_occurrences(s, element, i + 1) == count_occurrences(s, element, i)
{
    // This lemma is proven by the definition of count_occurrences
}

fn FindPositionOfElement(a: Vec<int>, Element: nat, n1: nat, s1: Seq<int>) -> (Position: int, Count: nat)
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall i:: 0<= i < s1.len() ==> a.spec_index(i) == s1.spec_index(i)
    ensures
        Position == -1 || Position >= 1,
        s1.len() != 0 && Position >= 1 ==> exists i:: 0 <= i < s1.len() && s1.spec_index(i) == Element,
        Position == -1 ==> forall i:: 0 <= i < s1.len() ==> s1.spec_index(i) != Element,
        Count == count_occurrences(s1, Element, s1.len() as int)
{
    let mut position: int = -1;
    let mut count: nat = 0;
    let mut i: usize = 0;
    
    while i < n1
        invariant
            0 <= i <= n1,
            n1 == s1.len(),
            position == -1 || position >= 1,
            count <= i,
            position == -1 ==> forall j:: 0 <= j < i ==> s1.spec_index(j) != Element,
            position >= 1 ==> exists j:: 0 <= j < i && s1.spec_index(j) == Element,
            count == count_occurrences(s1, Element, i as int),
            forall j:: 0 <= j < s1.len() ==> a.spec_index(j) == s1.spec_index(j)
    {
        let current_element = a[i];
        
        // Apply the lemma for count verification
        proof {
            lemma_count_increment(s1, Element, i as int);
        }
        
        // Check if current element equals Element (only if non-negative)
        if current_element >= 0 && current_element == (Element as int) {
            if position == -1 {
                position = (i + 1) as int;
            }
            count = count + 1;
            
            // Proof that we found an element
            assert(s1.spec_index(i as int) == current_element);
            assert(current_element == Element);
            assert(s1.spec_index(i as int) == Element);
            assert(exists j:: 0 <= j < (i + 1) && s1.spec_index(j) == Element);
        } else {
            // Proof that current element is not Element
            assert(s1.spec_index(i as int) == current_element);
            if current_element < 0 {
                assert(s1.spec_index(i as int) != Element);
            } else {
                assert(current_element != (Element as int));
                assert(s1.spec_index(i as int) != Element);
            }
        }
        
        i = i + 1;
    }
    
    // Final proof assertions
    assert(i == n1);
    assert(count == count_occurrences(s1, Element, n1 as int));
    assert(n1 as int == s1.len() as int);
    
    // Final postcondition proofs
    if position == -1 {
        assert(forall j:: 0 <= j < s1.len() ==> s1.spec_index(j) != Element);
    } else {
        assert(position >= 1);
        assert(exists j:: 0 <= j < s1.len() && s1.spec_index(j) == Element);
    }
    
    (position, count)
}

}