use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

fn main() {
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s.spec_index(j), s.spec_index(k))
}

spec fn below(first: Bases, second: Bases) -> bool {
    match (first, second) {
        (Bases::A, _) => true,
        (Bases::C, Bases::G) => true,
        (Bases::C, Bases::T) => true,
        (Bases::G, Bases::T) => true,
        (a, b) => a == b
    }
}

spec fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> Seq<Bases>
    recommends
        0 < s.len() && x < s.len() && y < s.len(),
{
    if x == y {
        s
    } else {
        let temp_x = s.spec_index(x as int);
        let temp_y = s.spec_index(y as int);
        let result1 = s.update(x as int, temp_y);
        let result2 = result1.update(y as int, temp_x);
        result2
    }
}

proof fn Exchanger_properties(s: Seq<Bases>, x: nat, y: nat)
    requires
        0 < s.len() && x < s.len() && y < s.len(),
    ensures
        Exchanger(s, x, y).len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> 
            Exchanger(s, x, y).spec_index(b) == s.spec_index(b),
        Exchanger(s, x, y).spec_index(x as int) == s.spec_index(y as int) && 
        s.spec_index(x as int) == Exchanger(s, x, y).spec_index(y as int),
{
    let t = Exchanger(s, x, y);
    
    if x == y {
        // When x == y, no swap occurs
        assert(t == s);
        assert(t.len() == s.len());
        assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> 
            t.spec_index(b) == s.spec_index(b));
        assert(t.spec_index(x as int) == s.spec_index(y as int));
        assert(s.spec_index(x as int) == t.spec_index(y as int));
    } else {
        // When x != y, perform the swap
        let temp_x = s.spec_index(x as int);
        let temp_y = s.spec_index(y as int);
        let result1 = s.update(x as int, temp_y);
        let result2 = result1.update(y as int, temp_x);
        
        // Prove length preservation
        assert(result1.len() == s.len()) by {
            // update preserves length
        };
        assert(result2.len() == result1.len()) by {
            // update preserves length
        };
        assert(t.len() == s.len());
        
        // Prove swap correctness
        assert(result2.spec_index(x as int) == temp_y) by {
            // After first update, position x has temp_y
            // Second update doesn't change position x (since x != y)
        };
        assert(result2.spec_index(y as int) == temp_x) by {
            // Second update puts temp_x at position y
        };
        
        // Prove other positions unchanged
        assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> {
            &&& result1.spec_index(b) == s.spec_index(b)
            &&& result2.spec_index(b) == result1.spec_index(b)
            &&& result2.spec_index(b) == s.spec_index(b)
        }) by {
            // update only changes the specified index
        };
        
        // Final assertions
        assert(t == result2);
        assert(t.spec_index(x as int) == s.spec_index(y as int));
        assert(s.spec_index(x as int) == t.spec_index(y as int));
    }
}

}