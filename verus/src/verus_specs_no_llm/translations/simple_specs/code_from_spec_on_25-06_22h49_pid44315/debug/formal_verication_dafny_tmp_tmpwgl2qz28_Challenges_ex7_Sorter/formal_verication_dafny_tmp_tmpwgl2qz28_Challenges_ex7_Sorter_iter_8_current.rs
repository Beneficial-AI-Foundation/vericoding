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
        forall|b: int| 0 <= b < s.len() && b != x as int && b != y as int ==> t[b] == s[b],
        t[x as int] == s[y as int] && t[y as int] == s[x as int],
{
    let x_int = x as int;
    let y_int = y as int;
    
    // Create the swapped sequence
    let result = s.update(x_int, s[y_int]).update(y_int, s[x_int]);
    
    // Proof block to help verification
    proof {
        // Length is preserved through updates
        assert(s.update(x_int, s[y_int]).len() == s.len());
        assert(result.len() == s.len());
        
        // The swap works correctly
        assert(result[x_int] == s[y_int]);
        assert(result[y_int] == s[x_int]);
        
        // Other positions are unchanged
        let temp = s.update(x_int, s[y_int]);
        assert(forall|i: int| 0 <= i < s.len() && i != x_int ==> temp[i] == s[i]);
        assert(forall|i: int| 0 <= i < temp.len() && i != y_int ==> result[i] == temp[i]);
        
        // Combine to show unchanged positions
        assert(forall|b: int| 0 <= b < s.len() && b != x_int && b != y_int ==> {
            result[b] == temp[b] && temp[b] == s[b]
        });
    }
    
    result
}

}