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
        // Trivial case - no swap needed
        assert(t == s);
    } else {
        let temp_x = s.spec_index(x as int);
        let temp_y = s.spec_index(y as int);
        let result1 = s.update(x as int, temp_y);
        let result2 = result1.update(y as int, temp_x);
        
        // Length is preserved through updates
        assert(result1.len() == s.len());
        assert(result2.len() == result1.len());
        
        // The swap property - values at x and y are swapped
        assert(result2.spec_index(x as int) == temp_y);
        assert(result2.spec_index(y as int) == temp_x);
        assert(temp_y == s.spec_index(y as int));
        assert(temp_x == s.spec_index(x as int));
        
        // For indices other than x and y, values remain unchanged
        assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> {
            result2.spec_index(b) == s.spec_index(b)
        });
        
        assert(t == result2);
    }
}

}