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
    
    while index < a.len()
        invariant 0 <= index <= a.len()
        invariant forall|i: int| 0 <= i < index && i <= a.len() - 3 ==> !(
            a[i] == a[i + 1] && 
            a[i + 1] == a[i + 2]
        )
    {
        if index + 2 < a.len() {
            if a[index] == a[index + 1] && a[index + 1] == a[index + 2] {
                assert(triple(a)) by {
                    assert(0 <= index < a.len() - 2);
                    assert(a[index as int] == a[index as int + 1] && 
                           a[index as int + 1] == a[index as int + 2]);
                }
                return index;
            }
        }
        index = index + 1;
    }
    
    // Prove that no triple exists when we reach here
    assert(!triple(a)) by {
        if triple(a) {
            let i = choose|i: int| 0 <= i < a.len() - 2 && 
                a[i] == a[i + 1] && a[i + 1] == a[i + 2];
            assert(0 <= i < index);
            assert(i <= a.len() - 3);
            assert(false); // Contradiction with invariant
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