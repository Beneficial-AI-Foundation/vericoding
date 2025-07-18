use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>) 
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
{
    let mut c: Set<char> = Set::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            // c contains exactly those elements that appear in a[0..i] and are in b
            forall|x: char| c.contains(x) <==> (exists|j: int| 0 <= j < i && a[j] == x && b.contains(x)),
    {
        if b.contains(a[i as int]) {
            c = c.insert(a[i as int]);
        }
        i = i + 1;
    }
    
    // After the loop, i == a.len(), so we need to prove the postcondition
    assert forall|x: char| c.contains(x) ==> (a.contains(x) && b.contains(x)) by {
        if c.contains(x) {
            // From loop invariant with i == a.len()
            assert(exists|j: int| 0 <= j < a.len() && a[j] == x && b.contains(x));
            // This directly gives us a.contains(x) && b.contains(x)
            assert(a.contains(x));
            assert(b.contains(x));
        }
    };
    
    assert forall|x: char| (a.contains(x) && b.contains(x)) ==> c.contains(x) by {
        if a.contains(x) && b.contains(x) {
            // If a.contains(x), then by definition of Seq::contains, there exists an index
            assert(exists|j: int| 0 <= j < a.len() && a[j] == x);
            // Since we also have b.contains(x), and i == a.len() after the loop,
            // the loop invariant tells us c.contains(x)
            assert(exists|j: int| 0 <= j < i && a[j] == x && b.contains(x));
        }
    };
    
    c
}

method TesterFilter() 
{
    let a = seq!['a', 'b', 'c', 'b', 'a'];
    let b = set!['a', 'c', 'd'];
    let c = Filter(a, b);
    
    // Test postcondition: elements in both a and b should be in c
    assert(c.contains('a')); // 'a' is in both a and b
    assert(c.contains('c')); // 'c' is in both a and b
    assert(!c.contains('b')); // 'b' is in a but not in b
    assert(!c.contains('d')); // 'd' is in b but not in a
}

}