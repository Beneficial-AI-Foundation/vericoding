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
        if s.spec_index((end - 1) as int) >= 0 && s.spec_index((end - 1) as int) as nat == element { 1 } else { 0 }
    }
}

// Lemma to help with count verification
proof fn lemma_count_increment(s: Seq<int>, element: nat, i: int)
    requires 
        i >= 0,
        i < s.len()
    ensures 
        (s.spec_index(i) >= 0 && s.spec_index(i) as nat == element) ==> 
            count_occurrences(s, element, i + 1) == count_occurrences(s, element, i) + 1,
        !(s.spec_index(i) >= 0 && s.spec_index(i) as nat == element) ==> 
            count_occurrences(s, element, i + 1) == count_occurrences(s, element, i)
{
    // The proof follows from the definition of count_occurrences
}

// Helper lemma for existential quantifier
proof fn lemma_exists_element(s: Seq<int>, element: nat, i: int)
    requires 
        i >= 0,
        i < s.len(),
        s.spec_index(i) >= 0,
        s.spec_index(i) as nat == element
    ensures exists j:: 0 <= j <= i && s.spec_index(j) >= 0 && s.spec_index(j) as nat == element
{
    assert(0 <= i <= i);
    assert(s.spec_index(i) >= 0 && s.spec_index(i) as nat == element);
}

// Lemma to establish the relationship between loop invariant and postcondition
proof fn lemma_extend_exists(s: Seq<int>, element: nat, i: int)
    requires 
        i >= 0,
        i <= s.len(),  // Changed from i < s.len() to i <= s.len()
        exists j:: 0 <= j < i && s.spec_index(j) >= 0 && s.spec_index(j) as nat == element
    ensures 
        exists j:: 0 <= j < s.len() && s.spec_index(j) >= 0 && s.spec_index(j) as nat == element
{
    // The proof follows from the fact that if there exists j in [0, i), 
    // then j is also in [0, s.len()) since i <= s.len()
}

fn FindPositionOfElement(a: Vec<int>, Element: nat, n1: nat, s1: Seq<int>) -> (Position: int, Count: nat)
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall i:: 0 <= i < s1.len() ==> a.spec_index(i) == s1.spec_index(i)
    ensures
        Position == -1 || Position >= 1,
        s1.len() != 0 && Position >= 1 ==> exists i:: 0 <= i < s1.len() && s1.spec_index(i) >= 0 && s1.spec_index(i) as nat == Element,
        Position == -1 ==> forall i:: 0 <= i < s1.len() ==> !(s1.spec_index(i) >= 0 && s1.spec_index(i) as nat == Element),
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
            position == -1 ==> forall j:: 0 <= j < i ==> !(s1.spec_index(j) >= 0 && s1.spec_index(j) as nat == Element),
            position >= 1 ==> exists j:: 0 <= j < i && s1.spec_index(j) >= 0 && s1.spec_index(j) as nat == Element,
            count == count_occurrences(s1, Element, i as int),
            forall j:: 0 <= j < s1.len() ==> a.spec_index(j) == s1.spec_index(j)
    {
        let current_element = a[i];
        
        proof {
            lemma_count_increment(s1, Element, i as int);
        }
        
        // Check if current element equals Element (only if non-negative)
        if current_element >= 0 && current_element as nat == Element {
            if position == -1 {
                position = (i + 1) as int;
            }
            count = count + 1;
            
            // Establish that we found an element at position i
            assert(s1.spec_index(i as int) == current_element);
            assert(current_element >= 0 && current_element as nat == Element);
            assert(s1.spec_index(i as int) >= 0 && s1.spec_index(i as int) as nat == Element);
            
            proof {
                lemma_exists_element(s1, Element, i as int);
            }
            
        } else {
            // Establish that current element is not Element
            assert(s1.spec_index(i as int) == current_element);
            if current_element < 0 {
                assert(!(s1.spec_index(i as int) >= 0 && s1.spec_index(i as int) as nat == Element));
            } else {
                assert(current_element as nat != Element);
                assert(!(s1.spec_index(i as int) >= 0 && s1.spec_index(i as int) as nat == Element));
            }
        }
        
        i = i + 1;
    }
    
    // Establish final postconditions
    assert(i == n1);
    assert(count == count_occurrences(s1, Element, n1 as int));
    assert(n1 as int == s1.len() as int);
    assert(count == count_occurrences(s1, Element, s1.len() as int));
    
    // Bridge the gap between loop invariant and postcondition
    if position >= 1 {
        assert(exists j:: 0 <= j < i && s1.spec_index(j) >= 0 && s1.spec_index(j) as nat == Element);
        assert(i == s1.len());
        proof {
            lemma_extend_exists(s1, Element, i as int);
        }
        assert(exists j:: 0 <= j < s1.len() && s1.spec_index(j) >= 0 && s1.spec_index(j) as nat == Element);
    }
    
    if position == -1 {
        assert(forall j:: 0 <= j < i ==> !(s1.spec_index(j) >= 0 && s1.spec_index(j) as nat == Element));
        assert(i == s1.len());
        assert(forall j:: 0 <= j < s1.len() ==> !(s1.spec_index(j) >= 0 && s1.spec_index(j) as nat == Element));
    }
    
    (position, count)
}

}