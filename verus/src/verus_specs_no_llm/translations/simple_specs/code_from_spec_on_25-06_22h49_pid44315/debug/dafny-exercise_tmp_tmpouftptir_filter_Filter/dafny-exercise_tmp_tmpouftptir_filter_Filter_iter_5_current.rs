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
            forall|x: char| x in result <==> (exists|j: int| 0 <= j < i && a[j] == x && x in b),
    {
        if b.contains(a[i]) {
            result = result.insert(a[i]);
        }
        i = i + 1;
    }
    
    // Prove the postcondition directly
    assert(forall|x: char| x in a && x in b <==> x in result) by {
        assert(forall|x: char| x in a && x in b ==> x in result) by {
            assert(forall|x: char| x in a ==> (exists|j: int| 0 <= j < a.len() && a[j] == x));
        }
        assert(forall|x: char| x in result ==> x in a && x in b) by {
            assert(forall|x: char| x in result ==> (exists|j: int| 0 <= j < a.len() && a[j] == x && x in b));
            assert(forall|x: char| (exists|j: int| 0 <= j < a.len() && a[j] == x) ==> x in a);
        }
    }
    
    result
}

}