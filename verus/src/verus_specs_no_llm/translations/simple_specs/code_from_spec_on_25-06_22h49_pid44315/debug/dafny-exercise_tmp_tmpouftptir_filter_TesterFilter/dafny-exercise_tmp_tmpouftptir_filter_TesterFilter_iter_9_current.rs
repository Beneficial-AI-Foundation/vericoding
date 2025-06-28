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
            forall|x: char| c.contains(x) <==> (exists|j: int| 0 <= j < i && a[j] == x) && b.contains(x),
    {
        if b.contains(a[i as int]) {
            c = c.insert(a[i as int]);
        }
        i = i + 1;
    }
    
    // After the loop, prove the postcondition
    assert(forall|x: char| c.contains(x) <==> (a.contains(x) && b.contains(x)));
    
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