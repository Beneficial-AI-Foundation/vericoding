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
        assert(!triple(a)) by {
            if exists|i: int| 0 <= i < a.len() - 2 && 
                a.spec_index(i) == a.spec_index(i + 1) && 
                a.spec_index(i + 1) == a.spec_index(i + 2) {
                let i = choose|i: int| 0 <= i < a.len() - 2 && 
                    a.spec_index(i) == a.spec_index(i + 1) && 
                    a.spec_index(i + 1) == a.spec_index(i + 2);
                assert(0 <= i < a.len() - 2);
                assert(a.len() < 3);
                assert(a.len() - 2 <= 1);
                assert(i < 1);
                assert(false);
            }
        }
        return a.len() as int;
    }
    
    let mut i: usize = 0;
    
    while i < a.len() - 2
        invariant
            0 <= i <= a.len() - 2,
            a.len() >= 3,
            forall|j: int| 0 <= j < i ==> !(a.spec_index(j) == a.spec_index(j + 1) && a.spec_index(j + 1) == a.spec_index(j + 2))
        decreases a.len() - 2 - i
    {
        assert(i < a.len() - 2);
        assert(i + 2 < a.len());
        if a[i] == a[i + 1] && a[i + 1] == a[i + 2] {
            assert(triple(a)) by {
                assert(0 <= i < a.len() - 2);
                assert(a.spec_index(i as int) == a.spec_index(i as int + 1) && a.spec_index(i as int + 1) == a.spec_index(i as int + 2));
            }
            return i as int;
        }
        i += 1;
    }
    
    assert(i == a.len() - 2);
    assert(!triple(a)) by {
        if exists|j: int| 0 <= j < a.len() - 2 && 
            a.spec_index(j) == a.spec_index(j + 1) && 
            a.spec_index(j + 1) == a.spec_index(j + 2) {
            let j = choose|j: int| 0 <= j < a.len() - 2 && 
                a.spec_index(j) == a.spec_index(j + 1) && 
                a.spec_index(j + 1) == a.spec_index(j + 2);
            assert(0 <= j < a.len() - 2);
            assert(j < i);
            assert(!(a.spec_index(j) == a.spec_index(j + 1) && a.spec_index(j + 1) == a.spec_index(j + 2)));
            assert(false);
        }
    }
    
    a.len() as int
}

}