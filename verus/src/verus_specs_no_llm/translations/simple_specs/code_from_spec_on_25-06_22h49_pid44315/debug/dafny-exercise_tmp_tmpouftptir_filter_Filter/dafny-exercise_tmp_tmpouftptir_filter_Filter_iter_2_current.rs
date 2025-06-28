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
    
    // After the loop, we need to prove the postcondition
    assert(forall|x: char| x in result <==> (exists|j: int| 0 <= j < a.len() && a[j] == x && x in b));
    assert(forall|x: char| (exists|j: int| 0 <= j < a.len() && a[j] == x && x in b) <==> (x in a && x in b));
    
    result
}

}