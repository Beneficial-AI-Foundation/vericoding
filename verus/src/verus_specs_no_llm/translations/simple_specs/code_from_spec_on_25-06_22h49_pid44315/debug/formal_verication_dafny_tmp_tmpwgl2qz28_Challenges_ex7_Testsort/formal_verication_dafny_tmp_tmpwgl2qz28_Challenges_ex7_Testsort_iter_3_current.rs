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
    first == second ||
    first == Bases::A ||
    (first == Bases::C && (second == Bases::G || second == Bases::T)) ||
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len(),
    ensures
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t.spec_index(b) == s.spec_index(b),
        t.spec_index(x as int) == s.spec_index(y as int) && s.spec_index(x as int) == t.spec_index(y as int),
{
    if x == y {
        s
    } else {
        let temp_x = s[x as int];
        let temp_y = s[y as int];
        let result1 = s.update(x as int, temp_y);
        let result2 = result1.update(y as int, temp_x);
        
        proof {
            assert(result2.len() == s.len()) by {
                assert(result1.len() == s.len());
            };
            
            assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> result2.spec_index(b) == s.spec_index(b)) by {
                assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> result1.spec_index(b) == s.spec_index(b));
                assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> b != y);
            };
            
            assert(result2.spec_index(x as int) == s.spec_index(y as int)) by {
                assert(x != y);
                assert(result1.spec_index(x as int) == temp_y);
                assert(temp_y == s.spec_index(y as int));
                assert(result2.spec_index(x as int) == result1.spec_index(x as int));
            };
            
            assert(result2.spec_index(y as int) == s.spec_index(x as int)) by {
                assert(result2.spec_index(y as int) == temp_x);
                assert(temp_x == s.spec_index(x as int));
            };
        }
        
        result2
    }
}

}