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
    
    // Store the original values
    let temp_x = s[x_int];
    let temp_y = s[y_int];
    
    // First update: set position x to value from position y
    let result1 = s.update(x_int, temp_y);
    
    // Second update: set position y to original value from position x
    let result2 = result1.update(y_int, temp_x);
    
    proof {
        // Prove length preservation
        assert(result1.len() == s.len());
        assert(result2.len() == result1.len());
        assert(result2.len() == s.len());
        
        // Prove the swap worked correctly
        assert(result2[x_int] == temp_y);
        assert(result2[x_int] == s[y_int]);
        assert(result2[y_int] == temp_x);
        assert(result2[y_int] == s[x_int]);
        
        // Prove other positions unchanged
        assert(forall|i: int| 0 <= i < s.len() && i != x_int ==> result1[i] == s[i]);
        assert(forall|i: int| 0 <= i < result1.len() && i != y_int ==> result2[i] == result1[i]);
        
        // Combine the facts to show positions other than x and y are unchanged
        assert(forall|b: int| 0 <= b < s.len() && b != x_int && b != y_int ==> {
            result2[b] == result1[b] && result1[b] == s[b]
        });
        
        // Final assertion for the postcondition
        assert(forall|b: int| 0 <= b < s.len() && b != x && b != y ==> {
            result2[b] == s[b]
        });
    }
    
    result2
}

}