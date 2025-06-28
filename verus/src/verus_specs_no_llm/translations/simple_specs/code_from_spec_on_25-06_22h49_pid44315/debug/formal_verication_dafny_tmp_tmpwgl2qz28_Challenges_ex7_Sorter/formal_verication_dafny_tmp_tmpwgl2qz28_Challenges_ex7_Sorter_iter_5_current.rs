use builtin::*;
use builtin_macros::*;

verus! {

// Define the Bases enum for DNA bases
#[derive(PartialEq, Eq)]
enum Bases {
    A,
    C,
    G,
    T,
}

fn main() {
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A ||
    (first == Bases::C && (second == Bases::G || second == Bases::T)) ||
    (first == Bases::G && second == Bases::T)
}

fn Exchanger(s: Seq<Bases>, x: usize, y: usize) -> (t: Seq<Bases>)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
    ensures
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
        t[x as int] == s[y as int] && t[y as int] == s[x as int],
{
    let x_int = x as int;
    let y_int = y as int;
    
    proof {
        assert(x < s.len());
        assert(y < s.len());
        assert(x_int < s.len());
        assert(y_int < s.len());
        assert(x_int >= 0);
        assert(y_int >= 0);
    }
    
    let temp = s[x_int];
    let result1 = s.update(x_int, s[y_int]);
    
    proof {
        assert(result1.len() == s.len());
        assert(result1[x_int] == s[y_int]);
        assert(forall|i: int| 0 <= i < s.len() && i != x_int ==> result1[i] == s[i]);
    }
    
    let result2 = result1.update(y_int, temp);
    
    proof {
        assert(result2.len() == result1.len());
        assert(result2.len() == s.len());
        assert(result2[y_int] == temp);
        assert(result2[y_int] == s[x_int]);
        assert(result2[x_int] == result1[x_int]);
        assert(result2[x_int] == s[y_int]);
        
        assert(forall|b: int| 0 <= b < s.len() && b != x_int && b != y_int ==> {
            result2[b] == result1[b] && result1[b] == s[b]
        });
        
        // Help verify the postcondition by establishing the connection between int and usize
        assert(forall|b: int| 0 <= b < s.len() && b != (x as int) && b != (y as int) ==> {
            b != x_int && b != y_int
        });
        
        assert(forall|b: int| 0 <= b < s.len() && b != (x as int) && b != (y as int) ==> {
            result2[b] == s[b]
        });
    }
    
    result2
}

}