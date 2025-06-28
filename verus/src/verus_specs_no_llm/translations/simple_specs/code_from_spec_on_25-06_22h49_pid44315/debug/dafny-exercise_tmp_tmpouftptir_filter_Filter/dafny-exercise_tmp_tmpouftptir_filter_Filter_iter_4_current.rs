use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures
        forall|x: char| x in a && x in b <==> x in c
{
    let mut result: Set<char> = Set::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            // Elements in result are exactly those that appear in a[0..i] and are in b
            forall|x: char| x in result <==> (exists|j: int| 0 <= j < i && a[j] == x && x in b),
    {
        if b.contains(a[i]) {
            result = result.insert(a[i]);
        }
        i = i + 1;
    }
    
    // After the loop, we have the invariant for the full range
    assert(forall|x: char| x in result <==> (exists|j: int| 0 <= j < a.len() && a[j] == x && x in b));
    
    // Now prove the postcondition
    assert(forall|x: char| x in a && x in b <==> x in result) by {
        // For any character x, show both directions of the equivalence
        assert(forall|x: char| x in a && x in b ==> x in result) by {
            // If x is in a and in b, then there exists an index j such that a[j] == x
            // and x in b, so x should be in result
            assert(forall|x: char| x in a ==> exists|j: int| 0 <= j < a.len() && a[j] == x);
        };
        
        assert(forall|x: char| x in result ==> x in a && x in b) by {
            // If x is in result, then by our invariant, there exists j such that
            // a[j] == x and x in b, which means x in a and x in b
            assert(forall|x: char| (exists|j: int| 0 <= j < a.len() && a[j] == x) ==> x in a);
        };
    };
    
    result
}

}