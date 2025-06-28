use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if there exists a triple of consecutive equal elements
spec fn triple(a: Vec<int>) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && 
        a.spec_index(i) == a.spec_index(i + 1) && 
        a.spec_index(i + 1) == a.spec_index(i + 2)
}

fn main() {
}

fn GetTriple(a: Vec<int>) -> (index: int)
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
        index == a.len() <==> !triple(a),
        0 <= index < a.len() - 2 <==> triple(a),
        0 <= index < a.len() - 2 ==> (a.spec_index(index) == a.spec_index(index + 1) && a.spec_index(index + 1) == a.spec_index(index + 2))
{
    if a.len() < 3 {
        return a.len();
    }
    
    let mut i = 0;
    
    while i < a.len() - 2
        invariant
            0 <= i <= a.len() - 2,
            a.len() >= 3,
            forall|j: int| 0 <= j < i ==> !(a.spec_index(j) == a.spec_index(j + 1) && a.spec_index(j + 1) == a.spec_index(j + 2))
    {
        if a[i] == a[i + 1] && a[i + 1] == a[i + 2] {
            return i;
        }
        i += 1;
    }
    
    a.len()
}

}