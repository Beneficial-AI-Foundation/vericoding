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
    // Handle case where array is too small to contain a triple
    if a.len() < 3 {
        assert(!triple(a)) by {
            if triple(a) {
                let i = choose|i: int| 0 <= i < a.len() - 2 && 
                    a[i] == a[i + 1] && a[i + 1] == a[i + 2];
                assert(0 <= i < a.len() - 2);
                assert(a.len() >= 3); // contradiction since i + 2 < a.len()
                assert(false);
            }
        }
        return a.len();
    }
    
    let mut index: usize = 0;
    
    while index <= a.len() - 3
        invariant 0 <= index <= a.len()
        invariant a.len() >= 3
        invariant index > a.len() - 3 ==> !triple(a)
        invariant forall|i: int| 0 <= i < index && i <= a.len() - 3 ==> !(
            a[i] == a[i + 1] && 
            a[i + 1] == a[i + 2]
        )
    {
        if a[index] == a[index + 1] && a[index + 1] == a[index + 2] {
            assert(triple(a)) by {
                assert(0 <= index <= a.len() - 3);
                assert(0 <= index < a.len() - 2);
                assert(a[index as int] == a[index as int + 1] && 
                       a[index as int + 1] == a[index as int + 2]);
            }
            return index;
        }
        index = index + 1;
    }
    
    // At this point, index > a.len() - 3, so we've checked all valid positions
    assert(!triple(a)) by {
        if triple(a) {
            let i = choose|i: int| 0 <= i < a.len() - 2 && 
                a[i] == a[i + 1] && a[i + 1] == a[i + 2];
            
            assert(0 <= i < a.len() - 2);
            assert(i <= a.len() - 3); // since i < a.len() - 2 and i is integer
            
            // We know index > a.len() - 3 from loop condition
            assert(index > a.len() - 3);
            assert(i < index);
            
            // But our invariant says no triple exists in [0, index)
            assert(0 <= i < index && i <= a.len() - 3);
            assert(!(a[i] == a[i + 1] && a[i + 1] == a[i + 2]));
            
            // Contradiction with the chosen witness
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