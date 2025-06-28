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
    proof {
        assert(x < s.len());
        assert(y < s.len());
        assert(x as int < s.len());
        assert(y as int < s.len());
    }
    
    let temp = s[x as int];
    let result1 = s.update(x as int, s[y as int]);
    
    proof {
        assert(result1.len() == s.len());
        assert(result1[x as int] == s[y as int]);
        assert(forall|i: int| 0 <= i < s.len() && i != x ==> result1[i] == s[i]);
    }
    
    let result2 = result1.update(y as int, temp);
    
    proof {
        assert(result2.len() == result1.len());
        assert(result2.len() == s.len());
        assert(result2[y as int] == temp);
        assert(result2[y as int] == s[x as int]);
        assert(result2[x as int] == result1[x as int]);
        assert(result2[x as int] == s[y as int]);
        
        assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> {
            result2[b] == result1[b] && result1[b] == s[b]
        });
    }
    
    result2
}

}