// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, horizontal: Seq<char>, vertical: Seq<char>) -> bool {
    n >= 2 && n <= 20 && m >= 2 && m <= 20 &&
    horizontal.len() == n && vertical.len() == m &&
    (forall|c: char| horizontal.contains(c) ==> c == '<' || c == '>') &&
    (forall|c: char| vertical.contains(c) ==> c == '^' || c == 'v')
}

spec fn is_disconnected(hor: Seq<char>, ver: Seq<char>) -> bool {
    (hor.len() > 0 && ver.len() > 0 && hor[0] == '>' && ver[0] == 'v') ||
    (hor.len() > 0 && ver.len() > 0 && hor[0] == '<' && ver[ver.len()-1] == 'v') ||
    (hor.len() > 0 && ver.len() > 0 && hor[hor.len()-1] == '>' && ver[0] == '^') ||
    (hor.len() > 0 && ver.len() > 0 && hor[hor.len()-1] == '<' && ver[ver.len()-1] == '^')
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, horizontal: Vec<char>, vertical: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(n as int, m as int, horizontal@, vertical@)
    ensures 
        result@ == seq!['Y', 'E', 'S', '\n'] || result@ == seq!['N', 'O', '\n'],
        (result@ == seq!['N', 'O', '\n']) <==> is_disconnected(horizontal@, vertical@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type error by using @ operator for Vec indexing */
    let mut result = Vec::new();
    
    // Assert bounds from precondition
    assert(horizontal@.len() == n as int);
    assert(vertical@.len() == m as int);
    assert(n >= 2 && m >= 2);
    assert(horizontal@.len() > 0);
    assert(vertical@.len() > 0);
    
    // Check each disconnection condition
    let cond1 = horizontal[0] == '>' && vertical[0] == 'v';
    let cond2 = horizontal[0] == '<' && vertical[(m - 1) as usize] == 'v';
    let cond3 = horizontal[(n - 1) as usize] == '>' && vertical[0] == '^';
    let cond4 = horizontal[(n - 1) as usize] == '<' && vertical[(m - 1) as usize] == '^';
    
    let disconnected = cond1 || cond2 || cond3 || cond4;
    
    // Prove equivalence with spec
    assert(horizontal@[0] == horizontal[0]);
    assert(vertical@[0] == vertical[0]);
    assert(horizontal@[horizontal@.len() - 1] == horizontal@[(n - 1) as int]);
    assert(vertical@[vertical@.len() - 1] == vertical@[(m - 1) as int]);
    assert(horizontal@[(n - 1) as int] == horizontal@[(n - 1) as int]);
    assert(vertical@[(m - 1) as int] == vertical@[(m - 1) as int]);
    
    assert(disconnected <==> is_disconnected(horizontal@, vertical@));
    
    if disconnected {
        result.push('N');
        result.push('O');
        result.push('\n');
        assert(result@ == seq!['N', 'O', '\n']);
    } else {
        result.push('Y');
        result.push('E');
        result.push('S');
        result.push('\n');
        assert(result@ == seq!['Y', 'E', 'S', '\n']);
    }
    
    result
}
// </vc-code>


}

fn main() {}