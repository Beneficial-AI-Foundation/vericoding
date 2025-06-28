use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>) 
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
{
    let mut c: Set<char> = Set::empty();
    let mut i: int = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall|x: char| c.contains(x) ==> (exists|j: int| 0 <= j < i && a[j] == x && b.contains(x)),
            forall|j: int| 0 <= j < i ==> (b.contains(a[j]) ==> c.contains(a[j])),
            forall|x: char| (exists|j: int| 0 <= j < i && a[j] == x && b.contains(x)) ==> c.contains(x)
    {
        if b.contains(a[i]) {
            c = c.insert(a[i]);
        }
        i = i + 1;
    }
    
    // Proof assertions to help establish the postcondition
    assert forall|x: char| c.contains(x) ==> (a.contains(x) && b.contains(x)) by {
        if c.contains(x) {
            assert(exists|j: int| 0 <= j < i && a[j] == x && b.contains(x));
            let j = choose|j: int| 0 <= j < i && a[j] == x && b.contains(x);
            assert(a.contains(x));
            assert(b.contains(x));
        }
    };
    
    assert forall|x: char| (a.contains(x) && b.contains(x)) ==> c.contains(x) by {
        if a.contains(x) && b.contains(x) {
            let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
            assert(0 <= j < i && a[j] == x && b.contains(x));
            assert(c.contains(x));
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