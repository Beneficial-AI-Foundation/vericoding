use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn triple(a: Vec<int>) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && 
        a[i] == a[i + 1] && 
        a[i + 1] == a[i + 2]
}

fn GetTriple(a: Vec<int>) -> (index: usize)
    requires a.len() >= 0
    ensures 0 <= index <= a.len()
    ensures (index == a.len()) <==> !triple(a)
    ensures (index < a.len()) ==> (index <= a.len() - 2)
    ensures (index < a.len()) <==> triple(a)
    ensures (index < a.len()) ==> (
        a[index as int] == a[index as int + 1] && 
        a[index as int + 1] == a[index as int + 2]
    )
{
    let mut index: usize = 0;
    
    while index + 2 < a.len()
        invariant 0 <= index <= a.len()
        invariant index + 2 >= a.len() ==> index >= a.len() - 2
        invariant forall|i: int| 0 <= i < index && i + 2 < a.len() ==> !(
            a[i] == a[i + 1] && 
            a[i + 1] == a[i + 2]
        )
    {
        if a[index] == a[index + 1] && a[index + 1] == a[index + 2] {
            assert(triple(a)) by {
                assert(0 <= index < a.len() - 2);
                assert(a[index as int] == a[index as int + 1] && 
                       a[index as int + 1] == a[index as int + 2]);
            }
            return index;
        }
        index = index + 1;
    }
    
    // At this point, index + 2 >= a.len(), so we've checked all valid positions
    assert(!triple(a)) by {
        if triple(a) {
            let i = choose|i: int| 0 <= i < a.len() - 2 && 
                a[i] == a[i + 1] && a[i + 1] == a[i + 2];
            
            // i must be a valid index for a triple
            assert(0 <= i < a.len() - 2);
            assert(i + 2 < a.len());
            
            // We know index + 2 >= a.len() from loop condition
            assert(index + 2 >= a.len());
            
            // Therefore i < index (since i + 2 < a.len() <= index + 2)
            assert(i + 2 < index + 2);
            assert(i < index);
            
            // But our invariant says no triple exists in [0, index)
            assert(0 <= i < index && i + 2 < a.len());
            assert(!(a[i] == a[i + 1] && a[i + 1] == a[i + 2]));
            
            // Contradiction
            assert(a[i] == a[i + 1] && a[i + 1] == a[i + 2]);
            assert(false);
        }
    }
    
    return a.len();
}

fn TesterGetTriple() -> (index: usize)
    ensures index == 0
{
    return 0;
}

}