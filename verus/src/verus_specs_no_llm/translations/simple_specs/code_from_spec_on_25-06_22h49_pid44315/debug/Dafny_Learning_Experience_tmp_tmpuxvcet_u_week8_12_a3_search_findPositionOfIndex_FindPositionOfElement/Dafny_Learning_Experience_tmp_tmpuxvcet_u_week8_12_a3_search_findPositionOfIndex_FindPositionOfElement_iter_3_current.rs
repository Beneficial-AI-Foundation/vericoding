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
            forall j:: 0 <= j < i ==> a.spec_index(j) == s1.spec_index(j)
    {
        if a[i] >= 0 && a[i] == Element {
            if position == -1 {
                position = (i + 1) as int;
            }
            count = count + 1;
        }
        
        // Add proof assertion to help with verification
        assert(count_occurrences(s1, Element, (i + 1) as int) == 
               count_occurrences(s1, Element, i as int) + 
               if s1.spec_index(i as int) == Element { 1 } else { 0 });
        
        i = i + 1;
    }
    
    (position, count)
}

}