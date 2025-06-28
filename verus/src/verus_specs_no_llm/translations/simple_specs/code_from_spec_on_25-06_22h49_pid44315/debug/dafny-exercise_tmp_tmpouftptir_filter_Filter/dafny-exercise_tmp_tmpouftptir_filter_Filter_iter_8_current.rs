use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures
        forall|x: char| x in c <==> (exists|j: int| 0 <= j < a.len() && a[j] == x && x in b)
{
    let mut result: Set<char> = Set::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: char| x in result <==> (exists|j: int| 0 <= j < i && a[j] == x && x in b),
    {
        if b.contains(a[i]) {
            result = result.insert(a[i]);
        }
        i = i + 1;
    }
    
    // Proof that the loop invariant implies the postcondition
    assert forall|x: char| x in result <==> (exists|j: int| 0 <= j < a.len() && a[j] == x && x in b) by {
        if x in result {
            // From loop invariant: exists j such that 0 <= j < i && a[j] == x && x in b
            // Since i == a.len() after the loop, this gives us what we need
            assert(exists|j: int| 0 <= j < a.len() && a[j] == x && x in b);
        }
        if exists|j: int| 0 <= j < a.len() && a[j] == x && x in b {
            // Since we processed all indices 0..a.len(), and x in b at some position j,
            // we would have added x to result when we processed index j
            assert(x in result);
        }
    };
    
    result
}

}