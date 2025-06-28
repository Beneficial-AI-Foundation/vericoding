use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures
        forall|x: char| x in c <==> (x in a && x in b)
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
    assert forall|x: char| x in result <==> (x in a && x in b) by {
        if x in result {
            // From loop invariant: exists j such that 0 <= j < a.len() && a[j] == x && x in b
            assert(x in a);
            assert(x in b);
        }
        if x in a && x in b {
            // x in a means exists some index where a[index] == x
            // Since we processed all indices 0..a.len(), and x in b, we added x to result
            assert(x in result);
        }
    };
    
    result
}

}