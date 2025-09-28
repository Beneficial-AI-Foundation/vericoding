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
/* helper modified by LLM (iteration 2): fixed lemma declaration */
proof fn disconnected_equiv(horizontal: &Vec<char>, vertical: &Vec<char>)
    requires
        valid_input(horizontal.len() as int, vertical.len() as int, horizontal@, vertical@)
    ensures
        is_disconnected(horizontal@, vertical@) == (
            (horizontal[0] == '>' && vertical[0] == 'v') ||
            (horizontal[0] == '<' && vertical[vertical.len()-1] == 'v') ||
            (horizontal[horizontal.len()-1] == '>' && vertical[0] == '^') ||
            (horizontal[horizontal.len()-1] == '<' && vertical[vertical.len()-1] == '^')
        )
{
    reveal(is_disconnected);
    assert(horizontal@.len() == horizontal.len() as int);
    assert(vertical@.len() == vertical.len() as int);
    assert(horizontal@[0] == horizontal[0]);
    assert(vertical@[0] == vertical[0]);
    assert(horizontal@[horizontal@.len()-1] == horizontal[horizontal.len()-1]);
    assert(vertical@[vertical@.len()-1] == vertical[vertical.len()-1]);
}
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
/* code modified by LLM (iteration 2): implemented condition check */
{
    let n = horizontal.len();
    let m = vertical.len();
    let cond = 
        (horizontal[0] == '>' && vertical[0] == 'v') ||
        (horizontal[0] == '<' && vertical[m-1] == 'v') ||
        (horizontal[n-1] == '>' && vertical[0] == '^') ||
        (horizontal[n-1] == '<' && vertical[m-1] == '^');

    proof {
        disconnected_equiv(&horizontal, &vertical);
    }

    if cond {
        vec!['N', 'O', '\n']
    } else {
        vec!['Y', 'E', 'S', '\n']
    }
}
// </vc-code>


}

fn main() {}